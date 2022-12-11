use crate::indices::{DefaultIndex, EdgeIndex, Indexable, NodeIndex};

/// A `Node` is used as the primary data structure in the `Graph`. It contains an index
/// and associated data of the node itself. 
///
/// # Type Parameters
/// * `N`: The type of the associated data.
/// * `Ix`: The type of the index. This is usually `DefaultIndex` which is `u32`.  
pub struct Node<N, Ix: Indexable = DefaultIndex> {
    /// The index of the node. This is used to identify the node in the graph.
    index: NodeIndex<Ix>,
    /// The associated data of the node.  
    inner: N,
}

impl<N, Ix: Indexable> Node<N, Ix> {
    pub fn new(idx: NodeIndex<Ix>, data: N) -> Self {
        Node {
            index: idx,
            inner: data,
        }
    }

    /// Returns the `NodeIndex` of the node.
    pub fn index(&self) -> &NodeIndex<Ix> {
        &self.index
    }

    /// Returns the associated data of the node.
    pub fn data(&self) -> &N {
        &self.inner
    }
}

/// An `Edge` represents the connection between two `Node`s in a `Graph`. It has a unique index
/// and a reference to the source and target `Node`s. Furthermore, it has associated data and a
/// weight.
///
/// # Type Parameters
/// * `E`: The type of the associated data.
/// * `Ix`: The type of the index. This is usually `DefaultIndex` which is `u32`.
pub struct Edge<E, Ix: Indexable = DefaultIndex> {
    /// The index of the edge. This is used to identify the edge in the graph.
    index: EdgeIndex<Ix>,
    /// The source and target node of the edge.
    node: [NodeIndex<Ix>; 2],
    /// The associated data of the edge.
    inner: E,
    /// The weight of the edge.
    weight: usize,
}

impl<E, Ix: Indexable> Edge<E, Ix> {
    pub fn new(idx: EdgeIndex<Ix>, source: NodeIndex<Ix>, target: NodeIndex<Ix>, data: E) -> Self {
        Edge {
            index: idx,
            inner: data,
            node: [source, target],
            weight: 1,
        }
    }

    pub fn new_weighted(
        idx: EdgeIndex<Ix>,
        source: NodeIndex<Ix>,
        target: NodeIndex<Ix>,
        data: E,
        weight: usize,
    ) -> Self {
        Edge {
            index: idx,
            inner: data,
            node: [source, target],
            weight,
        }
    }

    /// Returns the `EdgeIndex` of the edge.
    pub fn index(&self) -> &EdgeIndex<Ix> {
        &self.index
    }

    /// Returns the associated data of the edge.
    pub fn data(&self) -> &E {
        &self.inner
    }

    /// Returns the weight of the edge.
    pub fn weight(&self) -> usize {
        self.weight
    }

    /// Returns the `NodeIndex` of the source node.
    pub fn source(&self) -> &NodeIndex<Ix> {
        &self.node[0]
    }

    /// Returns the `NodeIndex` of the target node.
    pub fn target(&self) -> &NodeIndex<Ix> {
        &self.node[1]
    }
}

/// A `GraphKind` specifies the direction of edges in a `Graph`. It can be either `Directed`
/// or `Undirected`.
#[derive(Debug, PartialEq, Eq)]
pub enum GraphKind {
    Directed,
    Undirected,
}

#[derive(Debug, PartialEq, Eq)]
pub enum GraphError {
    NodeNotFound,
    EdgeNotFound,
}

/// A `Graph` is a data structure that can be used to represent a graph. It may
/// be `GraphKind::Directed` or `GraphKind::Undirected`. Furthermore, it has a list of
/// `Node`s and a list of `Edge`s.
///
/// # Type Parameters
/// * `N`: The type of the associated data of the nodes.
/// * `E`: The type of the associated data of the edges.
/// * `Ix`: The type of the index. This is usually `DefaultIndex` which is `u32`.
///
/// # Indices
/// To identify nodes and edges in the graph, indices are used. The indices are of type
/// `NodeIndex` and `EdgeIndex` respectively. The indices are not necessarily the same as
/// the index of the node or edge in the list of nodes or edges. It is important that the
/// indices satisfy the `Indexable` trait. The default indice type is `DefaultIndex` which
/// is `u32`.
///
/// * `NodeIndex`: The index of a node. This is used to identify the node in the graph.
/// * `EdgeIndex`: The index of an edge. This is used to identify the edge in the graph.
///
/// # Examples
/// A simple graph with nodes and edges of type `usize` and two nodes that have a
/// directed edge from node 1 to node 2:
/// ```
/// use graphed::graph::{Graph, GraphKind};
///
/// let mut gr = Graph::<usize, usize>::new(GraphKind::Directed);
/// let idx_node1 = gr.add_node(1);
/// let idx_node2 = gr.add_node(2);
/// gr.add_edge(idx_node1, idx_node2, 1);
/// ```
///
pub struct Graph<N, E, Ix: Indexable = DefaultIndex> {
    kind: GraphKind,
    nodes: Vec<Node<N, Ix>>,
    edges: Vec<Edge<E, Ix>>,
}

impl<N, E, Ix: Indexable> Graph<N, E, Ix> {
    pub fn new(kind: GraphKind) -> Self {
        Graph {
            kind,
            nodes: Vec::new(),
            edges: Vec::new(),
        }
    }

    /// Returns the kind of the graph.
    pub fn kind(&self) -> &GraphKind {
        &self.kind
    }

    /// Returns the number of nodes in the graph.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Returns the number of edges in the graph.
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    /// Add a node with associated data to the graph. Returns the `NodeIndex` of the new node.
    pub fn add_node(&mut self, data: N) -> NodeIndex<Ix> {
        let idx = NodeIndex::new(self.nodes.len());
        let node = Node::new(idx, data);
        self.nodes.push(node);

        idx
    }

    /// Add an edge from `source` to `target` with associated `data` to the graph. Before
    /// adding an edge to the graph it will be checked that the source and target nodes exist.
    /// If the edge is added successfully, the `EdgeIndex` of the new edge is returned.
    /// Otherwise, a `GraphError` is returned.
    pub fn add_edge(
        &mut self,
        source: NodeIndex<Ix>,
        target: NodeIndex<Ix>,
        data: E,
    ) -> Result<EdgeIndex<Ix>, GraphError> {
        // check if the source and target nodes exist
        if source.index() >= self.nodes.len() || target.index() >= self.nodes.len() {
            return Err(GraphError::NodeNotFound);
        }

        let idx = EdgeIndex::new(self.edges.len());
        let edge = Edge::new(idx, source, target, data);
        self.edges.push(edge);

        Ok(idx)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_add_node() {
        let mut graph = Graph::<usize, ()>::new(GraphKind::Directed);
        let idx = graph.add_node(1);

        assert_eq!(idx.index(), 0);
        assert_eq!(graph.node_count(), 1);
    }

    #[test]
    fn test_add_edge() {
        let mut graph = Graph::<usize, usize>::new(GraphKind::Directed);
        let source = graph.add_node(1);
        let target = graph.add_node(2);

        let idx = graph.add_edge(source, target, 3).unwrap();

        assert_eq!(idx.index(), 0);
        assert_eq!(graph.edge_count(), 1);
    }

    #[test]
    fn test_add_edge_error() {
        let mut graph = Graph::<usize, usize>::new(GraphKind::Directed);
        let source = graph.add_node(1);
        let target = graph.add_node(2);

        let idx = graph.add_edge(source, target, 3).unwrap();

        assert_eq!(idx.index(), 0);
        assert_eq!(graph.node_count(), 2);
        assert_eq!(graph.edge_count(), 1);

        // ensure that we get an GraphError::NodeNotFound when trying to add an edge with a non-existing...
        // ... source node
        let result = graph.add_edge(NodeIndex::new(4), target, 3);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), GraphError::NodeNotFound);

        // ... target node
        let result = graph.add_edge(source, NodeIndex::new(4), 3);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), GraphError::NodeNotFound);
    }
}
