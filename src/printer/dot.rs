use std::fmt::Write;

use crate::graph::{Graph, GraphKind};

static EDGE: [&'static str; 2] = ["->", "--"];
static TYPE: [&'static str; 2] = ["digraph", "graph"];

/// Prints a given `Graph` in the DOT format to the given `Write` object. The `Node`
/// and `Edge` types must satisfy the `Display` trait.
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
}
