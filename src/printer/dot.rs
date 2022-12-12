use std::fmt::Write;

use crate::graph::{Graph, GraphKind};

static EDGE: [&'static str; 2] = ["->", "--"];
static TYPE: [&'static str; 2] = ["digraph", "graph"];

/// Prints a given `Graph` in the DOT format to the given `Write` object. The `Node` 
/// and `Edge` types must satisfy the `Display` trait.
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
pub fn print_graph_dot<N, E>(graph: &Graph<N, E>, out: &mut dyn Write)
where
    N: std::fmt::Display,
    E: std::fmt::Display,
{
    let level = 1;
    let graph_type = match graph.kind() {
        GraphKind::Directed => TYPE[0],
        GraphKind::Undirected => TYPE[1],
    };

    writeln!(out, "{} {{", graph_type).unwrap();

    for node in graph.raw_nodes() {
        writeln!(
            out,
            "{}{} [label=\"{}\"];",
            " ".repeat(4 * level),
            node.index().index(),
            node.data()
        )
        .unwrap();
    }

    let edge_type = match graph.kind() {
        GraphKind::Directed => EDGE[0],
        GraphKind::Undirected => EDGE[1],
    };

    for edge in graph.raw_edges() {
        writeln!(
            out,
            "{}{} {} {} [label=\"{}\"];",
            " ".repeat(4 * level),
            edge.source().index(),
            edge_type,
            edge.target().index(),
            edge.data(),
        )
        .unwrap();
    }

    write!(out, "}}").unwrap();
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
        assert_eq!(
            out,
            "digraph {\n    0 [label=\"n1\"];\n    1 [label=\"n2\"];\n    0 -> 1 [label=\"123\"];\n}\n".trim()
        );
    }
}
