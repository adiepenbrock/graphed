use std::marker::PhantomData;

use crate::indices::{DefaultIndex, EdgeIndex, Indexable, NodeIndex};

/// A `Node` is used as the primary data structure in the `Graph`. It contains an index
/// and associated data of the node itself.
///
/// # Type Parameters
/// * `N`: The type of the associated data.
/// * `Ix`: The type of the index. This is usually `DefaultIndex` which is `u32`.  
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node<N, Ix: Indexable = DefaultIndex> {
    /// The index of the node. This is used to identify the node in the graph.
    index: NodeIndex<Ix>,
    /// The associated data of the node.  
    inner: N,
    /// A list of all incoming edges of the node.
    incoming: Vec<EdgeIndex<Ix>>,
    /// A list of all outgoing edges of the node.
    outgoing: Vec<EdgeIndex<Ix>>,
}

impl<N, Ix: Indexable> Node<N, Ix> {
    /// Creates a new [`Node`] with the given index and data.
    ///
    /// # Parameters
    ///
    /// * `idx` - The [`NodeIndex`] to assign to the new [`Node`].
    /// * `data` - The data to associate with the [`Node`].
    ///
    /// # Returns
    ///
    /// The newly created Node with empty incoming and outgoing edge lists.
    pub fn new(idx: NodeIndex<Ix>, data: N) -> Self {
        Node {
            index: idx,
            inner: data,
            incoming: Vec::new(),
            outgoing: Vec::new(),
        }
    }

    /// Returns the [`NodeIndex`] of the node.
    ///
    /// # Returns
    ///
    /// A reference to the [`NodeIndex`] that identifies this node.
    pub fn index(&self) -> &NodeIndex<Ix> {
        &self.index
    }

    /// Returns a reference to the data associated with this node.
    ///
    /// # Returns
    ///
    /// A reference to the node's data.
    pub fn data(&self) -> &N {
        &self.inner
    }

    /// Returns a slice reference to the incoming edge indices.
    ///
    /// # Returns
    ///
    /// A slice reference to the vector containing the indices of all incoming edges to this node.
    pub fn incoming(&self) -> &[EdgeIndex<Ix>] {
        &self.incoming
    }

    /// Returns a slice reference to the outgoing edge indices.
    ///
    /// # Returns
    ///
    /// A slice reference to the vector containing the indices of all outgoing edges from this node.
    pub fn outgoing(&self) -> &[EdgeIndex<Ix>] {
        &self.outgoing
    }
}

/// An `Edge` represents the connection between two `Node`s in a `Graph`. It has a unique index
/// and a reference to the source and target `Node`s. Furthermore, it has associated data and a
/// weight.
///
/// # Type Parameters
/// * `E`: The type of the associated data.
/// * `Ix`: The type of the index. This is usually `DefaultIndex` which is `u32`.
#[derive(Clone, Debug)]
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
    /// Creates a new [`Edge`] with the given index, source, target, and data.
    ///
    /// # Parameters
    ///
    /// * `idx` - The index to assign to the new [`Edge`].
    /// * `source` - The source [`NodeIndex`] for the [`Edge`].
    /// * `target` - The target [`NodeIndex`] for the [`Edge`].
    /// * `data` - The data to assign to the [`Edge`].
    ///
    /// # Returns
    ///  
    /// The newly created [`Edge`] with the provided index, source, target, and data.
    /// The weight is initialized to 1.
    pub fn new(idx: EdgeIndex<Ix>, source: NodeIndex<Ix>, target: NodeIndex<Ix>, data: E) -> Self {
        Edge {
            index: idx,
            inner: data,
            node: [source, target],
            weight: 1,
        }
    }

    /// Creates a new weighted [`Edge`] with the given parameters.
    ///
    /// # Parameters
    ///
    /// * `idx` - The index to assign to the new [`Edge`].
    /// * `source` - The source [`NodeIndex`] for the [`Edge`].
    /// * `target` - The target [`NodeIndex`] for the [`Edge`].
    /// * `data` - The data to assign to the [`Edge`].
    /// * `weight` - The weight to assign to the [`Edge`].
    ///
    /// # Returns
    ///
    /// The newly created weighted [`Edge`] with the provided parameters.
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

    /// Returns the [`EdgeIndex`] of the edge.
    ///
    /// # Returns
    ///
    /// A reference to the [`EdgeIndex`] that identifies this edge.
    pub fn index(&self) -> &EdgeIndex<Ix> {
        &self.index
    }

    /// Returns a reference to the data associated with this edge.
    ///
    /// # Returns
    ///
    /// A reference to the edge's data.
    pub fn data(&self) -> &E {
        &self.inner
    }

    /// Returns the weight of the edge.
    ///
    /// # Returns
    ///
    /// The weight of the edge as a `usize`.
    pub fn weight(&self) -> usize {
        self.weight
    }

    /// Returns a reference to the source [`NodeIndex`] of this edge.
    ///
    /// # Returns
    ///
    /// A reference to the [`NodeIndex`] of the source node.
    pub fn source(&self) -> &NodeIndex<Ix> {
        &self.node[0]
    }

    /// Returns a reference to the target [`NodeIndex`] of this edge.
    ///
    /// # Returns
    ///
    /// A reference to the [`NodeIndex`] of the target node.
    pub fn target(&self) -> &NodeIndex<Ix> {
        &self.node[1]
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum GraphError {
    NodeNotFound,
    EdgeNotFound,
}

pub trait EdgeType {
    fn is_directed() -> bool;
}

#[derive(Copy, Clone, Debug)]
pub struct Directed {}

impl EdgeType for Directed {
    #[inline]
    fn is_directed() -> bool {
        true
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Undirected {}

impl EdgeType for Undirected {
    #[inline]
    fn is_directed() -> bool {
        false
    }
}

/// A `Graph` is a data structure that can be used to represent a graph. Furthermore, it
/// has a list of `Node`s and a list of `Edge`s.
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
/// use graphed::graph::DiGraph;
///
/// let mut gr = DiGraph::<usize, usize>::new();
/// let idx_node1 = gr.add_node(1);
/// let idx_node2 = gr.add_node(2);
/// gr.add_edge(idx_node1, idx_node2, 1);
/// ```
///
#[derive(Clone, Debug)]
pub struct Graph<N, E, Ty = Directed, Ix: Indexable = DefaultIndex> {
    nodes: Vec<Node<N, Ix>>,
    edges: Vec<Edge<E, Ix>>,
    ty: PhantomData<Ty>,
}

/// Type alias for a directed Graph.
///
/// # Type Parameters
///
/// * `N` - The node data type.
/// * `E` - The edge data type.  
/// * `Ix` - The index type, default is [`DefaultIndex`].
///
/// # Example
///
/// ```rust
/// // Create a directed graph with u32 node and edge types
/// let graph: DiGraph<u32, u32> = DiGraph::new();
/// ```
pub type DiGraph<N, E, Ix = DefaultIndex> = Graph<N, E, Directed, Ix>;

/// Type alias for an undirected Graph.
///
/// # Type Parameters
///
/// * `N` - The node data type.
/// * `E` - The edge data type.
/// * `Ix` - The index type, default is [`DefaultIndex`].
///
/// # Example
///
/// ```rust
/// // Create an undirected graph with u32 node and edge types
/// let graph: UnGraph<u32, u32> = UnGraph::new();
/// ```
pub type UnGraph<N, E, Ix = DefaultIndex> = Graph<N, E, Undirected, Ix>;

impl<N, E> Graph<N, E, Directed> {
    /// Creates a new empty directed Graph.
    ///
    /// # Returns  
    ///
    /// A new directed Graph with empty nodes and edges vectors.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Graph {
            nodes: Vec::new(),
            edges: Vec::new(),
            ty: PhantomData,
        }
    }
}

impl<N, E> Graph<N, E, Undirected> {
    /// Creates a new empty undirected Graph.
    ///
    /// # Returns  
    ///
    /// A new undirected Graph with empty nodes and edges vectors.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Graph {
            nodes: Vec::new(),
            edges: Vec::new(),
            ty: PhantomData,
        }
    }
}

impl<N, E, Ty, Ix: Indexable> Graph<N, E, Ty, Ix>
where
    Ty: EdgeType,
{
    /// Creates a new Graph with pre-allocated capacity for nodes and edges.
    ///
    /// # Parameters
    ///
    /// * `nodes` - The capacity for the node vector.
    /// * `edges` - The capacity for the edge vector.  
    ///
    /// # Returns
    ///   
    /// A new Graph with pre-allocated capacity for nodes and edges.
    ///
    /// # Behavior
    ///
    /// Uses `Vec::with_capacity` to pre-allocate capacity for the node and edge vectors when
    /// creating the Graph.
    pub fn with_capacity(nodes: usize, edges: usize) -> Self {
        Graph {
            nodes: Vec::with_capacity(nodes),
            edges: Vec::with_capacity(edges),
            ty: PhantomData,
        }
    }

    /// Returns whether the graph is directed.
    ///
    /// # Returns
    ///
    /// True if the graph is directed, false if undirected.
    ///
    /// # Behavior
    ///
    /// Calls the `is_directed()` method on the graph's edge type `Ty` to determine if edges are
    /// directed.
    #[inline]
    pub fn is_directed(&self) -> bool {
        Ty::is_directed()
    }

    /// Returns the number of nodes in the graph.
    ///
    /// # Returns
    ///
    /// The number of nodes in the graph as a `usize`.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Returns the number of edges in the graph.
    ///
    /// # Returns
    ///
    /// The number of edges in the graph as a `usize`.
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    /// Returns a reference to the raw internal vector of Nodes.
    ///
    /// # Returns
    ///
    /// A slice reference to the vector of Nodes.
    pub fn raw_nodes(&self) -> &[Node<N, Ix>] {
        &self.nodes
    }

    /// Returns a reference to the raw internal vector of Edges.
    ///
    /// # Returns
    ///
    /// A slice reference to the vector of Edges.
    pub fn raw_edges(&self) -> &[Edge<E, Ix>] {
        &self.edges
    }

    /// Adds a new node to the graph with the given data.
    ///
    /// # Parameters
    ///
    /// * `data` - The data to associate with the new node.
    ///
    /// # Returns  
    ///
    /// The [`NodeIndex`] of the newly added node.
    ///
    /// # Behavior
    ///
    /// - Creates a new [`Node`] with the next available index and the given data.
    /// - Adds the new [`Node`] to the nodes vector.
    /// - Returns the index of the new [`Node`].
    pub fn add_node(&mut self, data: N) -> NodeIndex<Ix> {
        let idx = NodeIndex::new(self.nodes.len());
        let node = Node::new(idx, data);
        self.nodes.push(node);

        idx
    }

    /// Adds a new directed edge to the graph between the given source and target nodes.
    ///
    /// # Parameters
    ///
    /// * `source` - The [`NodeIndex`] of the source node.
    /// * `target` - The [`NodeIndex`] of the target node.
    /// * `data` - The data to associate with the new edge.
    ///
    /// # Returns
    ///
    /// Returns the index of the new edge if added successfully.
    /// Returns a [`GraphError`] if either node does not exist.
    ///
    /// # Behavior
    ///
    /// - Checks that the source and target nodes exist.
    /// - Creates a new [`Edge`] with the given data between the nodes.
    /// - Adds the new edge index to the outgoing edges of the source node.
    /// - Adds the new edge index to the incoming edges of the target node.
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

        // add incoming and outgoing edges to the source and target node
        self.nodes
            .get_mut(source.index())
            .unwrap()
            .outgoing
            .push(idx);
        self.nodes
            .get_mut(target.index())
            .unwrap()
            .incoming
            .push(idx);

        Ok(idx)
    }

    /// Gets an immutable reference to the [`Node`] with the given index.
    ///
    /// # Parameters
    ///
    /// * `idx` - The [`NodeIndex`] of the [`Node`] to get.
    ///
    /// # Returns
    ///
    /// Returns a reference to the Node if found.
    /// Returns None if no Node exists with the given index.
    pub fn get_node(&self, idx: NodeIndex<Ix>) -> Option<&Node<N, Ix>> {
        self.nodes.get(idx.index())
    }

    /// Gets a mutable reference to the Node with the given index.
    ///
    /// # Parameters
    ///
    /// * `idx` - The [`NodeIndex`] of the [`Node`] to get.
    ///
    /// # Returns
    ///  
    /// Returns a mutable reference to the [`Node`] if found.
    /// Returns None if no Node exists with the given index.
    pub fn get_node_mut(&mut self, idx: NodeIndex<Ix>) -> Option<&mut Node<N, Ix>> {
        self.nodes.get_mut(idx.index())
    }

    /// Checks if an edge exists between the given source and target node indices.
    ///
    /// # Parameters
    ///
    /// * `source` - The [`NodeIndex`] of the source node.
    /// * `target` - The [`NodeIndex`] of the target node.
    ///
    /// # Returns
    ///
    /// True if an edge exists between the nodes, false otherwise.
    pub fn has_edge(&self, source: &NodeIndex<Ix>, target: &NodeIndex<Ix>) -> bool {
        self.find_edge(source, target).is_some()
    }

    /// Finds the first node in the graph that matches the given filter function.
    ///
    /// # Parameters
    ///
    /// * `filter` - A function that takes a reference to a [`Node`] and returns a bool.
    ///
    /// # Returns
    ///
    /// Returns a reference to the first [`Node`] where `filter` returns `true`.
    /// Returns `None` if no node matches the filter.
    ///
    /// # Example
    ///
    /// ```rust
    /// use graphed::{Graph, Node};
    ///
    /// let mut graph = DiGraph::<&str, ()>::new();
    /// _ = graph.add_node("target");
    /// let node = graph.find_node(|node| node.data() == "target");
    /// ```
    pub fn find_node(&self, filter: impl Fn(&Node<N, Ix>) -> bool) -> Option<&Node<N, Ix>> {
        self.nodes.iter().find(|n| filter(n))
    }

    /// Finds an edge between the given source and target node indices.
    ///
    /// For undirected graphs, searches for an undirected edge between the nodes.
    /// For directed graphs, searches for a directed edge from the source to the target.
    ///
    /// # Parameters
    ///
    /// * `source` - The [`NodeIndex`] of the source node.
    /// * `target` - The [`NodeIndex`] of the target node.  
    ///
    /// # Returns
    ///
    /// Returns the [`EdgeIndex`] if an edge exists between the nodes.
    /// Returns None if no edge exists.
    ///
    /// # Behavior
    ///
    /// - For undirected graphs, checks both the outgoing edges of the source node and the incoming
    /// edges of the target node.
    /// - For directed graphs, checks only the outgoing edges of the source node.
    pub fn find_edge(
        &self,
        source: &NodeIndex<Ix>,
        target: &NodeIndex<Ix>,
    ) -> Option<&EdgeIndex<Ix>> {
        if !self.is_directed() {
            self.find_undirected_edge(source, target)
        } else {
            match self.nodes.get(source.index()) {
                Some(node) => self.find_directed_edge(&node.index, target),
                None => None,
            }
        }
    }

    /// Finds a directed edge between the given source and target node indices.
    ///
    /// # Parameters
    ///
    /// * `source` - The [`NodeIndex`] of the source node.
    /// * `target` - The [`NodeIndex`] of the target node.
    ///
    /// # Returns  
    ///
    /// Returns the edge index of the directed edge from source to target if found.
    /// Returns None if no directed edge exists from source to target.
    ///
    /// # Description
    ///
    /// This checks only the outgoing edges of the source node to find an edge that has the target
    /// node as its target. Since this is a directed graph, the edge must go specifically from the
    /// source to the target node.
    pub fn find_directed_edge(
        &self,
        source: &NodeIndex<Ix>,
        target: &NodeIndex<Ix>,
    ) -> Option<&EdgeIndex<Ix>> {
        let node = &self.nodes[source.index()];
        for eidx in node.outgoing() {
            let edge = match self.edges.get(eidx.index()) {
                Some(e) => e,
                None => return None,
            };
            if edge.target().index() == target.index() {
                return Some(eidx);
            }
        }
        None
    }

    /// Finds an undirected edge between the given source and target node indices.
    ///
    /// # Parameters
    ///
    /// * `source` - The [`NodeIndex`] of the source node.
    /// * `target` - The [`NodeIndex`] of the target node.
    ///
    /// # Returns
    ///
    /// Returns the edge index of the undirected edge between the source and target nodes if found.
    /// Returns None if no undirected edge exists between the nodes.
    ///
    /// # Description
    ///
    /// This checks the outgoing edges of the source node and the incoming edges of the target node
    /// to find an edge that connects the two nodes in either direction. Since this is an undirected
    /// graph, the edge can go from source to target or from target to source.
    pub fn find_undirected_edge(
        &self,
        source: &NodeIndex<Ix>,
        target: &NodeIndex<Ix>,
    ) -> Option<&EdgeIndex<Ix>> {
        let node = &self.nodes[source.index()];

        for eidx in node.outgoing() {
            let edge = match self.edges.get(eidx.index()) {
                Some(e) => e,
                None => return None,
            };
            if edge.target().index() == target.index() {
                return Some(eidx);
            }
        }
        for eidx in node.incoming() {
            let edge = match self.edges.get(eidx.index()) {
                Some(e) => e,
                None => return None,
            };
            if edge.source().index() == target.index() {
                return Some(eidx);
            }
        }

        None
    }

    /// Returns a list of all `NodeIndex`es that are direct predecessors of the given `node`.
    pub fn predecessor_of_node(&self, idx: NodeIndex<Ix>) -> Vec<&NodeIndex<Ix>> {
        let mut predecessors = Vec::new();

        for edge in &self.nodes[idx.index()].incoming {
            predecessors.push(self.edges[edge.index()].source());
        }

        predecessors
    }
}

impl<N, E, Ty, Ix: Indexable> std::ops::Index<NodeIndex<Ix>> for Graph<N, E, Ty, Ix> {
    type Output = Node<N, Ix>;

    fn index(&self, index: NodeIndex<Ix>) -> &Self::Output {
        &self.nodes[index.index()]
    }
}

impl<N, E, Ty, Ix: Indexable> std::ops::Index<EdgeIndex<Ix>> for Graph<N, E, Ty, Ix> {
    type Output = Edge<E, Ix>;

    fn index(&self, index: EdgeIndex<Ix>) -> &Self::Output {
        &self.edges[index.index()]
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_add_node() {
        let mut graph = DiGraph::<usize, ()>::new();
        let idx = graph.add_node(1);

        assert_eq!(idx.index(), 0);
        assert_eq!(graph.node_count(), 1);
    }

    #[test]
    fn test_add_edge() {
        let mut graph = DiGraph::<usize, usize>::new();
        let source = graph.add_node(1);
        let target = graph.add_node(2);

        let idx = graph.add_edge(source, target, 3).unwrap();

        assert_eq!(idx.index(), 0);
        assert_eq!(graph.edge_count(), 1);
    }

    #[test]
    fn test_add_edge_error() {
        let mut graph = DiGraph::<usize, usize>::new();
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

    #[test]
    fn test_add_in_out_coming_index_to_node() {
        let mut graph = DiGraph::<usize, usize>::new();
        let source = graph.add_node(1);
        let target = graph.add_node(2);

        let idx = graph.add_edge(source, target, 3).unwrap();

        assert_eq!(idx.index(), 0);
        assert_eq!(graph.node_count(), 2);
        assert_eq!(graph.edge_count(), 1);
        assert_eq!(graph.nodes[source.index()].outgoing, vec![idx]);
        assert_eq!(graph.nodes[target.index()].incoming, vec![idx]);
    }

    #[test]
    fn test_get_predecessor_of_node() {
        let mut graph = DiGraph::<usize, usize>::new();
        let idx_1 = graph.add_node(1);
        let idx_2 = graph.add_node(2);
        let idx_3 = graph.add_node(3);
        let _ = graph.add_edge(idx_1, idx_2, 42);
        let _ = graph.add_edge(idx_2, idx_3, 84);

        // because the method `predecessor_of_node` returns just a list of the direct
        // predecessors, the list should only contain the node `idx_2`...
        let pred = graph.predecessor_of_node(idx_3);
        assert_eq!(pred.len(), 1);
        assert_eq!(pred[0].index(), idx_2.index());
        assert_eq!(pred, vec![&idx_2]);
    }

    #[test]
    fn test_find_edge_directed() {
        let mut graph = DiGraph::<usize, usize>::new();
        let idx_1 = graph.add_node(1);
        let idx_2 = graph.add_node(2);
        let idx_3 = graph.add_node(3);
        let _ = graph.add_edge(idx_1, idx_2, 42);
        let _ = graph.add_edge(idx_2, idx_3, 84);

        let e1 = graph.find_edge(&idx_1, &idx_2);
        assert!(e1.is_some());
        assert_eq!(e1.unwrap().index(), 0);
        let e2 = graph.find_directed_edge(&idx_1, &idx_2);
        assert!(e2.is_some());
        assert_eq!(e2.unwrap().index(), 0);
    }

    #[test]
    fn test_find_edge_undirected() {
        let mut graph = UnGraph::<usize, usize>::new();
        let idx_1 = graph.add_node(1);
        let idx_2 = graph.add_node(2);
        let idx_3 = graph.add_node(3);
        let _ = graph.add_edge(idx_1, idx_2, 42);
        let _ = graph.add_edge(idx_2, idx_3, 84);

        let e1 = graph.find_edge(&idx_1, &idx_2);
        assert!(e1.is_some());
        assert_eq!(e1.unwrap().index(), 0);
        let e2 = graph.find_undirected_edge(&idx_1, &idx_2);
        assert!(e2.is_some());
        assert_eq!(e2.unwrap().index(), 0);

        let e3 = graph.find_undirected_edge(&idx_2, &idx_1);
        assert!(e3.is_some());
        assert_eq!(e3.unwrap().index(), 0);
    }

    #[test]
    fn test_index_graph_by_nodeindex() {
        let mut g = DiGraph::<usize, usize>::new();
        let n1 = g.add_node(1);
        let n2 = g.add_node(2);

        assert_eq!(*g[n1].data(), 1);
        assert_eq!(*g[n2].data(), 2);
    }

    #[test]
    fn test_index_graph_by_edgeindex() {
        let mut g = DiGraph::<usize, usize>::new();
        let n1 = g.add_node(1);
        let n2 = g.add_node(2);
        let e1 = g.add_edge(n1, n2, 3).unwrap();

        assert_eq!(*g[n1].data(), 1);
        assert_eq!(*g[n2].data(), 2);
        assert_eq!(*g[e1].data(), 3);
    }
}
