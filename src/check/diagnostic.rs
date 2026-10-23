//! Bounded read-only term rendering for tests and introspection builds.
//! No access here evaluates, normalizes, reduces, checks, or charges semantic work.
use crate::check::delayed::environment::{EnvId, Environment};
use crate::syntax::expressions::{BinderInfo, ExprId, ExprKind, Expressions};
use crate::syntax::levels::{LevelId, LevelKind, Levels, NameId};
use crate::syntax::local_context::LocalContext;
use crate::syntax::names::{DiagnosticComponent, Names};
use std::fmt::{self, Write};
use std::mem::size_of;

const MAX_OUTPUT: usize = 16_384;
const MAX_NODES: usize = 256;
const MAX_FRAMES: usize = MAX_NODES * 3;
const MAX_NAME_COMPONENTS: usize = 128;
const OUTPUT_ELISION: &[u8] = b"\n... output-byte-limit\n";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Limits {
    depth: u32,
    nodes: u16,
    bytes: u16,
    name_components: u16,
}
impl Limits {
    pub(crate) const DEFAULT: Self = Self {
        depth: 64,
        nodes: 256,
        bytes: 16_384,
        name_components: 128,
    };

    pub(crate) fn new(depth: u32, nodes: u16, bytes: u16) -> Option<Self> {
        (depth > 0
            && usize::from(nodes) <= MAX_NODES
            && nodes > 0
            && usize::from(bytes) <= MAX_OUTPUT
            && usize::from(bytes) >= OUTPUT_ELISION.len())
        .then_some(Self {
            depth,
            nodes,
            bytes,
            name_components: depth.min(MAX_NAME_COMPONENTS as u32) as u16,
        })
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Truncated {
    pub depth: bool,
    pub nodes: bool,
    pub edges: bool,
    pub output_bytes: bool,
    pub name: bool,
}

pub(crate) struct Rendered {
    bytes: [u8; MAX_OUTPUT],
    len: usize,
    truncated: Truncated,
}
const _: () = assert!(size_of::<Rendered>() <= MAX_OUTPUT + 16);

#[derive(Clone, Copy)]
pub(crate) struct Sources<'a> {
    pub expressions: &'a Expressions,
    pub levels: &'a Levels,
    pub names: &'a Names,
    pub locals: Option<&'a LocalContext>,
}
impl Rendered {
    pub(crate) fn as_bytes(&self) -> &[u8] {
        &self.bytes[..self.len]
    }

    pub(crate) fn as_str(&self) -> &str {
        // All source strings were validated as UTF-8 and writes never split a
        // source character or escape token.
        std::str::from_utf8(self.as_bytes()).unwrap_or("... invalid diagnostic UTF-8")
    }

    pub(crate) fn truncation(&self) -> Truncated {
        self.truncated
    }
}

struct Output {
    bytes: [u8; MAX_OUTPUT],
    len: usize,
    limit: usize,
    truncated: bool,
}
impl Output {
    fn new(limit: usize) -> Self {
        Self {
            bytes: [0; MAX_OUTPUT],
            len: 0,
            limit,
            truncated: false,
        }
    }

    fn token(&mut self, token: &[u8]) -> bool {
        if self.truncated {
            return false;
        }
        let payload_limit = self.limit - OUTPUT_ELISION.len();
        let Some(end) = self.len.checked_add(token.len()) else {
            self.truncated = true;
            return false;
        };
        if end > payload_limit {
            self.truncated = true;
            return false;
        }
        self.bytes[self.len..end].copy_from_slice(token);
        self.len = end;
        true
    }

    fn escaped(&mut self, text: &[u8]) {
        let _ = self.token(b"\"");
        let mut offset = 0;
        while offset < text.len() {
            if self.truncated {
                break;
            }
            let width = match text[offset] {
                0x00..=0x7f => 1,
                0xc2..=0xdf => 2,
                0xe0..=0xef => 3,
                0xf0..=0xf4 => 4,
                _ => {
                    let _ = self.token(b"<invalid-utf8>");
                    break;
                }
            };
            let Some(end) = offset.checked_add(width).filter(|end| *end <= text.len()) else {
                let _ = self.token(b"<invalid-utf8>");
                break;
            };
            let Ok(fragment) = std::str::from_utf8(&text[offset..end]) else {
                let _ = self.token(b"<invalid-utf8>");
                break;
            };
            let ch = fragment.chars().next().unwrap_or('\u{fffd}');
            match ch {
                '"' => {
                    let _ = self.token(b"\\\"");
                }
                '\\' => {
                    let _ = self.token(b"\\\\");
                }
                '\n' => {
                    let _ = self.token(b"\\n");
                }
                '\r' => {
                    let _ = self.token(b"\\r");
                }
                '\t' => {
                    let _ = self.token(b"\\t");
                }
                c if c.is_control()
                    || matches!(
                        c,
                        '\u{061c}'
                            | '\u{200e}'
                            | '\u{200f}'
                            | '\u{202a}'..='\u{202e}'
                            | '\u{2066}'..='\u{2069}'
                    ) =>
                {
                    let _ = write!(self, "\\u{:04x}", c as u32);
                }
                c => {
                    let mut bytes = [0; 4];
                    let _ = self.token(c.encode_utf8(&mut bytes).as_bytes());
                }
            }
            offset = end;
        }
        let _ = self.token(b"\"");
    }

    fn finish(mut self, flags: &mut Truncated) -> Rendered {
        if self.truncated {
            let end = self.len + OUTPUT_ELISION.len();
            self.bytes[self.len..end].copy_from_slice(OUTPUT_ELISION);
            self.len = end;
            flags.output_bytes = true;
        }
        Rendered {
            bytes: self.bytes,
            len: self.len,
            truncated: *flags,
        }
    }
}
impl Write for Output {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        self.token(text.as_bytes()).then_some(()).ok_or(fmt::Error)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Node {
    Expression(ExprId),
    Level(LevelId),
    Local(u32),
    Environment(EnvId),
}

struct Printer<'a> {
    expressions: &'a Expressions,
    levels: &'a Levels,
    names: &'a Names,
    locals: Option<&'a LocalContext>,
    environments: Option<&'a Environment>,
    limits: Limits,
    output: Output,
    flags: Truncated,
    seen: [Option<Node>; MAX_NODES],
    seen_len: usize,
    frames: [Option<(Node, u32)>; MAX_FRAMES],
    frame_len: usize,
    variadic_edges_remaining: usize,
}
const _: () = assert!(size_of::<Printer<'static>>() <= 32 * 1024);

impl<'a> Printer<'a> {
    fn new(
        expressions: &'a Expressions,
        levels: &'a Levels,
        names: &'a Names,
        locals: Option<&'a LocalContext>,
        environments: Option<&'a Environment>,
        limits: Limits,
    ) -> Self {
        Self {
            expressions,
            levels,
            names,
            locals,
            environments,
            limits,
            output: Output::new(usize::from(limits.bytes)),
            flags: Truncated::default(),
            seen: [None; MAX_NODES],
            seen_len: 0,
            frames: [None; MAX_FRAMES],
            frame_len: 0,
            variadic_edges_remaining: usize::from(limits.nodes),
        }
    }

    fn push(&mut self, node: Node, depth: u32) {
        if self.frame_len == MAX_FRAMES {
            self.flags.nodes = true;
            return;
        }
        self.frames[self.frame_len] = Some((node, depth));
        self.frame_len += 1;
    }

    fn pop(&mut self) -> Option<(Node, u32)> {
        self.frame_len = self.frame_len.checked_sub(1)?;
        self.frames[self.frame_len].take()
    }

    fn reference(&mut self, node: Node) {
        match node {
            Node::Expression(id) => {
                let _ = write!(self.output, "%e{}", id.slot());
            }
            Node::Level(id) => {
                let _ = write!(self.output, "%u{}", id.slot());
            }
            Node::Local(id) => {
                let _ = write!(self.output, "%l{id}");
            }
            Node::Environment(id) => {
                let _ = write!(self.output, "%v{}", id.diagnostic_slot());
            }
        }
    }

    fn schedule(&mut self, node: Node, depth: u32) {
        self.reference(node);
        self.push(node, depth);
    }

    fn name(&mut self, id: NameId) {
        let _ = write!(self.output, "%n{}:[", id.0);
        let mut path = [None; MAX_NAME_COMPONENTS];
        let mut len = 0usize;
        let mut current = id;
        loop {
            match self.names.diagnostic_component(current) {
                Ok(Some((prefix, _))) if len < usize::from(self.limits.name_components) => {
                    path[len] = Some(current);
                    len += 1;
                    current = prefix;
                }
                Ok(Some(_)) => {
                    self.flags.name = true;
                    let _ = self.output.token(b"...,");
                    break;
                }
                Ok(None) => break,
                Err(_) => {
                    let _ = self.output.token(b"<invalid-name>");
                    break;
                }
            }
        }
        for position in (0..len).rev() {
            if position + 1 != len {
                let _ = self.output.token(b",");
            }
            let component = self
                .names
                .diagnostic_component(path[position].unwrap())
                .ok()
                .flatten();
            match component.map(|(_, component)| component) {
                Some(DiagnosticComponent::Number(number)) => {
                    let _ = self.output.token(b"#");
                    let _ = self.output.token(number);
                }
                Some(DiagnosticComponent::String(text)) => self.output.escaped(text),
                None => {
                    let _ = self.output.token(b"<invalid-name>");
                }
            }
        }
        let _ = self.output.token(b"]");
    }

    fn binder(&mut self, kind: &str, id: ExprId, name: NameId, annotation: BinderInfo) {
        let _ = write!(self.output, "{kind} binder=%b{} name=", id.slot());
        self.name(name);
        let _ = write!(self.output, " info={}", binder_info(annotation));
    }

    fn render_expression(&mut self, id: ExprId, depth: u32) {
        self.reference(Node::Expression(id));
        let _ = self.output.token(b" = ");
        let Ok(kind) = self.expressions.diagnostic_kind(id, self.levels) else {
            let _ = self.output.token(b"<invalid-expression>\n");
            return;
        };
        match kind {
            ExprKind::Bound(index) => {
                let _ = writeln!(self.output, "bound #{index}");
            }
            ExprKind::Free(local) => {
                let _ = self.output.token(b"free ");
                self.schedule(Node::Local(local), depth.saturating_add(1));
                let _ = self.output.token(b"\n");
            }
            ExprKind::Sort(level) => {
                let _ = self.output.token(b"sort ");
                self.schedule(Node::Level(level), depth.saturating_add(1));
                let _ = self.output.token(b"\n");
            }
            ExprKind::App(function, argument) => {
                let _ = self.output.token(b"app ");
                self.reference(Node::Expression(function));
                let _ = self.output.token(b" ");
                self.schedule(Node::Expression(argument), depth.saturating_add(1));
                self.push(Node::Expression(function), depth.saturating_add(1));
                let _ = self.output.token(b"\n");
            }
            ExprKind::Lambda(name, domain, body, annotation)
            | ExprKind::Pi(name, domain, body, annotation) => {
                self.binder(
                    if matches!(kind, ExprKind::Lambda(..)) {
                        "lambda"
                    } else {
                        "pi"
                    },
                    id,
                    name,
                    annotation,
                );
                let _ = self.output.token(b" domain=");
                self.reference(Node::Expression(domain));
                let _ = self.output.token(b" body=");
                self.schedule(Node::Expression(body), depth.saturating_add(1));
                self.push(Node::Expression(domain), depth.saturating_add(1));
                let _ = self.output.token(b"\n");
            }
            ExprKind::Constant(name, arguments) => {
                let _ = self.output.token(b"const ");
                self.name(name);
                let _ = self.output.token(b" universes=[");
                let edge_limit = arguments.len().min(self.variadic_edges_remaining);
                let mut rendered = 0;
                for (index, level) in arguments.iter().take(edge_limit).enumerate() {
                    if index != 0 {
                        let _ = self.output.token(b",");
                    }
                    self.reference(Node::Level(*level));
                    if self.output.truncated {
                        return;
                    }
                    rendered += 1;
                }
                self.variadic_edges_remaining -= rendered;
                if rendered < arguments.len() {
                    self.flags.edges = true;
                    if rendered != 0 {
                        let _ = self.output.token(b",");
                    }
                    let _ = self.output.token(b"...<edge-limit>");
                }
                let _ = self.output.token(b"]\n");
                if self.output.truncated {
                    return;
                }
                for level in arguments[..rendered].iter().rev() {
                    self.push(Node::Level(*level), depth.saturating_add(1));
                }
            }
            ExprKind::Let(name, ty, value, body, nondependent) => {
                self.binder("let", id, name, BinderInfo::Default);
                let _ = write!(self.output, " nondependent={nondependent} type=");
                self.reference(Node::Expression(ty));
                let _ = self.output.token(b" value=");
                self.reference(Node::Expression(value));
                let _ = self.output.token(b" body=");
                self.schedule(Node::Expression(body), depth.saturating_add(1));
                self.push(Node::Expression(value), depth.saturating_add(1));
                self.push(Node::Expression(ty), depth.saturating_add(1));
                let _ = self.output.token(b"\n");
            }
            ExprKind::Projection(name, index, target) => {
                let _ = self.output.token(b"projection structure=");
                self.name(name);
                let _ = write!(self.output, " field={index} target=");
                self.schedule(Node::Expression(target), depth.saturating_add(1));
                let _ = self.output.token(b"\n");
            }
            ExprKind::Natural(number) => {
                let _ = self.output.token(b"natural ");
                let _ = self.output.token(number);
                let _ = self.output.token(b"\n");
            }
            ExprKind::String(text) => {
                let _ = self.output.token(b"string ");
                // Installation validated the whole payload. Decode only the
                // bounded prefix that can reach this diagnostic output.
                self.output.escaped(text);
                let _ = self.output.token(b"\n");
            }
            ExprKind::MData(payload, wrapped) => {
                let _ = self.output.token(b"mdata ");
                // Installation validated the whole payload. Decode only the
                // bounded prefix that can reach this diagnostic output.
                self.output.escaped(payload);
                let _ = self.output.token(b" wrapped=");
                self.schedule(Node::Expression(wrapped), depth.saturating_add(1));
                let _ = self.output.token(b"\n");
            }
        }
    }

    fn render_level(&mut self, id: LevelId, depth: u32) {
        self.reference(Node::Level(id));
        let _ = self.output.token(b" = ");
        match self.levels.diagnostic_kind(id) {
            Ok(LevelKind::Zero) => {
                let _ = self.output.token(b"zero\n");
            }
            Ok(LevelKind::Succ(child)) => {
                let _ = self.output.token(b"succ ");
                self.schedule(Node::Level(child), depth.saturating_add(1));
                let _ = self.output.token(b"\n");
            }
            Ok(LevelKind::Max(left, right)) => {
                let _ = self.output.token(b"max ");
                self.reference(Node::Level(left));
                let _ = self.output.token(b" ");
                self.schedule(Node::Level(right), depth.saturating_add(1));
                self.push(Node::Level(left), depth.saturating_add(1));
                let _ = self.output.token(b"\n");
            }
            Ok(LevelKind::IMax(left, right)) => {
                let _ = self.output.token(b"imax ");
                self.reference(Node::Level(left));
                let _ = self.output.token(b" ");
                self.schedule(Node::Level(right), depth.saturating_add(1));
                self.push(Node::Level(left), depth.saturating_add(1));
                let _ = self.output.token(b"\n");
            }
            Ok(LevelKind::Param(name)) => {
                let _ = self.output.token(b"parameter ");
                self.name(name);
                let _ = self.output.token(b"\n");
            }
            Err(_) => {
                let _ = self.output.token(b"<invalid-level>\n");
            }
        }
    }

    fn render_local(&mut self, id: u32, depth: u32) {
        self.reference(Node::Local(id));
        let _ = self.output.token(b" = ");
        let Some((local, active)) = self.locals.and_then(|locals| locals.diagnostic_get(id)) else {
            let _ = self.output.token(b"<local-unavailable>\n");
            return;
        };
        let _ = write!(self.output, "local active={active} name=");
        self.name(local.name());
        let _ = write!(
            self.output,
            " info={} type=",
            binder_info(local.annotation())
        );
        self.reference(Node::Expression(local.ty()));
        if let Some(value) = local.value() {
            let _ = self.output.token(b" value=");
            self.schedule(Node::Expression(value), depth.saturating_add(1));
        }
        self.push(Node::Expression(local.ty()), depth.saturating_add(1));
        let _ = self.output.token(b"\n");
    }

    fn render_environment(&mut self, id: EnvId, depth: u32) {
        self.reference(Node::Environment(id));
        let _ = self.output.token(b" = environment [");
        let Some(environments) = self.environments else {
            let _ = self.output.token(b"<environment-unavailable>]\n");
            return;
        };
        let Ok(len) = environments.diagnostic_len(id) else {
            let _ = self.output.token(b"<invalid-environment>]\n");
            return;
        };
        let edge_limit = usize::try_from(len)
            .unwrap_or(usize::MAX)
            .min(self.variadic_edges_remaining);
        let mut rendered = 0;
        for index in 0..edge_limit {
            if index != 0 {
                let _ = self.output.token(b", ");
            }
            let _ = write!(self.output, "#{index}=");
            match environments.diagnostic_lookup(id, index as u32) {
                Ok(binding) => self.reference(Node::Expression(ExprId::diagnostic_from_slot(
                    binding.slot(),
                ))),
                Err(_) => {
                    let _ = self.output.token(b"<invalid-binding>");
                }
            }
            if self.output.truncated {
                return;
            }
            rendered += 1;
        }
        self.variadic_edges_remaining -= rendered;
        if rendered < usize::try_from(len).unwrap_or(usize::MAX) {
            self.flags.edges = true;
            if rendered != 0 {
                let _ = self.output.token(b", ");
            }
            let _ = self.output.token(b"...<bindings-limit>");
        }
        let _ = self.output.token(b"]\n");
        if self.output.truncated {
            return;
        }
        for index in (0..rendered).rev() {
            if let Ok(binding) = environments.diagnostic_lookup(id, index as u32) {
                self.push(
                    Node::Expression(ExprId::diagnostic_from_slot(binding.slot())),
                    depth.saturating_add(1),
                );
            }
        }
    }

    fn finish(mut self) -> Rendered {
        while let Some((node, depth)) = self.pop() {
            if self.output.truncated {
                break;
            }
            if depth > self.limits.depth {
                self.flags.depth = true;
                self.reference(node);
                let _ = self.output.token(b" = <depth-limit>\n");
                continue;
            }
            if self.seen[..self.seen_len].contains(&Some(node)) {
                continue;
            }
            if self.seen_len == usize::from(self.limits.nodes) {
                self.flags.nodes = true;
                break;
            }
            self.seen[self.seen_len] = Some(node);
            self.seen_len += 1;
            match node {
                Node::Expression(id) => self.render_expression(id, depth),
                Node::Level(id) => self.render_level(id, depth),
                Node::Local(id) => self.render_local(id, depth),
                Node::Environment(id) => self.render_environment(id, depth),
            }
        }
        if self.flags.nodes && !self.output.truncated {
            let _ = self.output.token(b"... node-limit\n");
        }
        self.output.finish(&mut self.flags)
    }
}

fn binder_info(info: BinderInfo) -> &'static str {
    match info {
        BinderInfo::Default => "default",
        BinderInfo::Implicit => "implicit",
        BinderInfo::StrictImplicit => "strict-implicit",
        BinderInfo::InstanceImplicit => "instance-implicit",
    }
}

pub(crate) fn term(root: ExprId, sources: Sources<'_>, limits: Limits) -> Rendered {
    let mut printer = Printer::new(
        sources.expressions,
        sources.levels,
        sources.names,
        sources.locals,
        None,
        limits,
    );
    let _ = printer.output.token(b"root=");
    printer.schedule(Node::Expression(root), 0);
    let _ = printer.output.token(b"\n");
    printer.finish()
}

pub(crate) fn name(root: NameId, sources: Sources<'_>, limits: Limits) -> Rendered {
    let mut printer = Printer::new(
        sources.expressions,
        sources.levels,
        sources.names,
        sources.locals,
        None,
        limits,
    );
    let _ = printer.output.token(b"name=");
    printer.name(root);
    let _ = printer.output.token(b"\n");
    printer.finish()
}

pub(crate) fn delayed(
    root: ExprId,
    environment: EnvId,
    sources: Sources<'_>,
    environments: &Environment,
    limits: Limits,
) -> Rendered {
    let mut printer = Printer::new(
        sources.expressions,
        sources.levels,
        sources.names,
        sources.locals,
        Some(environments),
        limits,
    );
    let _ = printer.output.token(b"root=delayed(expression=");
    printer.reference(Node::Expression(root));
    let _ = printer.output.token(b", environment=");
    printer.schedule(Node::Environment(environment), 0);
    printer.push(Node::Expression(root), 0);
    let _ = printer.output.token(b")\n");
    printer.finish()
}

// The printer lands before its failure-snapshot caller. These compile-time
// references keep the introspection-only interface checked without adding code,
// data, or a production symbol; the next diagnostics slice calls it directly.
#[cfg(feature = "introspection")]
const _: () = {
    let _ = Limits::DEFAULT;
    let _ = Limits::new;
    let _ = Rendered::as_bytes;
    let _ = Rendered::as_str;
    let _ = Rendered::truncation;
    let _ = term;
    let _ = name;
    let _ = delayed;
};
