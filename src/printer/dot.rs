use std::fmt::{Display, Write};

use crate::graph::{Edge, Graph, GraphKind, Node};

static EDGE: [&'static str; 2] = ["->", "--"];
static TYPE: [&'static str; 2] = ["digraph", "graph"];

pub mod attributes {
    /// Text label attached to objects.
    pub const LABEL: &'static str = "label";
    /// The shape of a node.
    pub const SHAPE: &'static str = "shape";
    /// Basic drawing color for graphics, not text.
    pub const COLOR: &'static str = "color";
    /// Color used for text.
    pub const FONTCOLOR: &'static str = "fontcolor";
}

/// `Attributes` can be used to customize the layout of DOT elements, i.e., `Node`s, `Edge`s or
/// `Graph`s. Please note that the attribute names and values are case-sensetive in DOT.
/// A list of supported attributes can be found here: [https://graphviz.org/doc/info/attrs.html]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attributes {
    inner: Vec<(&'static str, String)>,
}

/// A wrapper that contains all attributes for a specific element, i.e., `Node`s or `Edge`s.
impl Attributes {
    /// Creates a new instance of `Attributes`.
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    /// Add a new entry to the the list of attributes.
    pub fn add<T: Into<String>>(&mut self, key: &'static str, value: T) {
        self.inner.push((key, value.into()));
    }

    /// Removes an entry from the attributes.
    pub fn remove(&mut self, key: &'static str) {
        match self.inner.iter().position(|(k, _)| k.eq(&key)) {
            Some(pos) => self.inner.remove(pos),
            _ => return,
        };
    }
}

impl Display for Attributes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let bar = self
            .inner
            .iter()
            .map(|(key, value)| format!("{} = \"{}\"", key, value))
            .collect::<Vec<String>>()
            .join(", ");
        write!(f, "[{}]", bar)
    }
}

/// Transforms a `Graph` into a DOT-formatted string representation and writes it to a given
/// output target, `out`. The output target must implement the `std::fmt::Writer` trait.
/// Furthermore, it supports the annotation of `Node`s and `Edge`s with attributes such as labels,
/// shapes, or colors. A list of supported attributes by DOT can be found
/// here: [https://graphviz.org/doc/info/attrs.html].
///
/// # Type parameters
/// * `N`: The type of the nodes in the graph.
/// * `E`: The type of the edges in the graph.
///
/// # Example
/// To print a graph into a `String` and print it to the console:
/// ```
/// use graphed::graph::{Graph, GraphKind, Node, Edge};
/// use graphed::printer::dot::{print_graph_dot_extended, Attributes};
///
/// let mut gr = Graph::<&str, usize>::new(GraphKind::Directed);
/// let idx_n1 = gr.add_node("n1");
/// let idx_n2 = gr.add_node("n2");
/// gr.add_edge(idx_n1, idx_n2, 123);
///
/// let node_renderer = |node: &Node<&str>| -> Option<Attributes> {
///     let mut attrs = Attributes::new();
///     attrs.add("label", node.data().to_string());
///
///     Some(attrs)
/// };
///
/// let edge_renderer = |edge: &Edge<usize>| -> Option<Attributes> {
///     let mut attrs = Attributes::new();
///     attrs.add("label", edge.data().to_string());
///
///     Some(attrs)
/// };
///
/// let mut out = String::new();
/// print_graph_dot_extended(&gr, &mut out, &node_renderer, &edge_renderer);
/// println!("{}", out);
/// ```
pub fn print_graph_dot_extended<N, E>(
    graph: &Graph<N, E>,
    out: &mut dyn Write,
    node_renderer: &dyn Fn(&Node<N>) -> Option<Attributes>,
    edge_renderer: &dyn Fn(&Edge<E>) -> Option<Attributes>,
) {
    let mut buf = String::new();

    let level = 1;
    let (graph_type, edge_type) = match graph.kind() {
        GraphKind::Directed => (TYPE[0], EDGE[0]),
        GraphKind::Undirected => (TYPE[1], EDGE[1]),
    };

    buf.push_str(&format!("{} {{\n", graph_type));

    for node in graph.raw_nodes() {
        match node_renderer(node) {
            Some(attrs) => {
                buf.push_str(&format!(
                    "{}{} {};\n",
                    " ".repeat(4 * level),
                    node.index().index(),
                    attrs
                ));
            }
            None => {
                buf.push_str(&format!(
                    "{}{};\n",
                    " ".repeat(4 * level),
                    node.index().index()
                ));
            }
        };
    }

    for edge in graph.raw_edges() {
        match edge_renderer(edge) {
            Some(attrs) => {
                buf.push_str(&format!(
                    "{}{} {} {} {};\n",
                    " ".repeat(4 * level),
                    edge.source().index(),
                    edge_type,
                    edge.target().index(),
                    attrs
                ));
            }
            None => {
                buf.push_str(&format!(
                    "{}{} {} {};\n",
                    " ".repeat(4 * level),
                    edge.source().index(),
                    edge_type,
                    edge.target().index()
                ));
            }
        }
    }

    buf.push_str("}");
    out.write_str(buf.as_str()).unwrap();
}

/// Transforms a `Graph` into a simple DOT-formatted string representation and writes it to a given
/// output target, `out`. The output target must implement the `std::fmt::Writer` trait. Please
/// note that this function does not support the annotation of attributes to elements. To get
/// an extended version of this function that also supports attributes, please see
/// `print_graph_dot_extended`.
///
/// # Type parameters
/// * `N`: The type of the nodes in the graph.
/// * `E`: The type of the edges in the graph.
///
/// # Example
/// To print a graph into a `String` and print it to the console:
/// ```
/// use graphed::graph::{Graph, GraphKind};
/// use graphed::printer::dot::print_graph_dot;
///
/// let mut gr = Graph::<&str, usize>::new(GraphKind::Directed);
/// let idx_n1 = gr.add_node("n1");
/// let idx_n2 = gr.add_node("n2");
/// gr.add_edge(idx_n1, idx_n2, 123);
///
/// let mut out = String::new();
/// print_graph_dot(&gr, &mut out);
/// println!("{}", out);
/// ```
pub fn print_graph_dot<N, E>(graph: &Graph<N, E>, out: &mut dyn Write) {
    let mut buf = String::new();

    let level = 1;
    let (graph_type, edge_type) = match graph.kind() {
        GraphKind::Directed => (TYPE[0], EDGE[0]),
        GraphKind::Undirected => (TYPE[1], EDGE[1]),
    };

    buf.push_str(&format!("{} {{\n", graph_type));

    for node in graph.raw_nodes() {
        buf.push_str(&format!(
            "{}{};\n",
            " ".repeat(4 * level),
            node.index().index()
        ));
    }

    for edge in graph.raw_edges() {
        buf.push_str(&format!(
            "{}{} {} {};\n",
            " ".repeat(4 * level),
            edge.source().index(),
            edge_type,
            edge.target().index()
        ));
    }

    buf.push_str("}");
    out.write_str(buf.as_str()).unwrap();
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::graph::{Edge, Node};

    #[test]
    fn test_print_simple_digraph_with_dot() {
        let mut gr = Graph::<&str, usize>::new(GraphKind::Directed);
        let idx_n1 = gr.add_node("n1");
        let idx_n2 = gr.add_node("n2");
        let _ = gr.add_edge(idx_n1, idx_n2, 123);

        let mut out = String::new();
        print_graph_dot(&gr, &mut out);
        assert_eq!(out, "digraph {\n    0;\n    1;\n    0 -> 1;\n}".trim());
    }

    #[test]
    fn test_print_attributed_digraph_with_dot() {
        let mut gr = Graph::<&str, usize>::new(GraphKind::Directed);
        let idx_n1 = gr.add_node("n1");
        let idx_n2 = gr.add_node("n2");
        let _ = gr.add_edge(idx_n1, idx_n2, 123);

        let node_printer = |node: &Node<&str>| -> Option<Attributes> {
            let mut attrs = Attributes::new();
            attrs.add(attributes::LABEL, node.data().to_string());
            attrs.add(attributes::FONTCOLOR, "red");

            Some(attrs)
        };

        let edge_printer = |edge: &Edge<usize>| -> Option<Attributes> {
            let mut attrs = Attributes::new();
            attrs.add(attributes::LABEL, edge.data().to_string());

            Some(attrs)
        };

        let mut out = String::new();
        print_graph_dot_extended(&gr, &mut out, &node_printer, &edge_printer);
        assert_eq!(
            out,
            "digraph {\n    0 [label = \"n1\", fontcolor = \"red\"];\n    1 [label = \"n2\", fontcolor = \"red\"];\n    0 -> 1 [label = \"123\"];\n}".trim()
        );
    }
}
