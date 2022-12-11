use std::{fmt, hash::Hash};

/// The default index type that is used in graphs.
pub type DefaultIndex = u32;

/// A trait that is used to create indicies for nodes and edges. Currenty, we only support numeric
/// indices so that we implement this trait for `usize`, `u32`, `u16` and `u8`.
pub trait Indexable: Copy + Default + Hash + Ord + fmt::Debug + 'static {
    /// Creates a new index from  the given `usize`.
    fn new(ix: usize) -> Self;

    /// Returns the index as `usize`.
    fn index(&self) -> usize;
}

impl Indexable for usize {
    fn new(ix: usize) -> Self {
        ix
    }

    fn index(&self) -> usize {
        *self
    }
}

impl Indexable for u32 {
    fn new(ix: usize) -> Self {
        ix as u32
    }

    fn index(&self) -> usize {
        *self as usize
    }
}

impl Indexable for u16 {
    fn new(ix: usize) -> Self {
        ix as u16
    }

    fn index(&self) -> usize {
        *self as usize
    }
}

impl Indexable for u8 {
    fn new(ix: usize) -> Self {
        ix as u8
    }

    fn index(&self) -> usize {
        *self as usize
    }
}

/// A index that is used for nodes.
#[derive(Copy, Clone, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct NodeIndex<Ix = DefaultIndex>(Ix);

impl<Ix: Indexable> NodeIndex<Ix> {
    /// Creates a new `NodeIndex` from the given `usize`.
    pub fn new(index: usize) -> Self {
        NodeIndex(Indexable::new(index))
    }

    /// Returns the value of the particular index as `usize`.
    pub fn index(&self) -> usize {
        self.0.index()
    }
}

impl<Ix: Indexable> Indexable for NodeIndex<Ix> {
    fn new(ix: usize) -> Self {
        NodeIndex::new(ix)
    }

    fn index(&self) -> usize {
        self.0.index()
    }
}

impl<Ix: Indexable> From<Ix> for NodeIndex<Ix> {
    fn from(index: Ix) -> Self {
        NodeIndex(index)
    }
}

impl<Ix: fmt::Debug> fmt::Debug for NodeIndex<Ix> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "NodeIndex({:?})", self.0)
    }
}

impl<Ix: fmt::Display> fmt::Display for NodeIndex<Ix> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A index that is used for edges.
#[derive(Copy, Clone, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct EdgeIndex<Ix = DefaultIndex>(Ix);

impl<Ix: Indexable> EdgeIndex<Ix> {
    /// Creates a new `EdgeIndex` from the given `usize`.
    pub fn new(index: usize) -> Self {
        EdgeIndex(Indexable::new(index))
    }

    /// Returns the value of the particular index as `usize`.
    pub fn index(&self) -> usize {
        self.0.index()
    }
}

impl<Ix: Indexable> Indexable for EdgeIndex<Ix> {
    fn new(ix: usize) -> Self {
        EdgeIndex::new(ix)
    }

    fn index(&self) -> usize {
        self.0.index()
    }
}

impl<Ix: Indexable> From<Ix> for EdgeIndex<Ix> {
    fn from(index: Ix) -> Self {
        EdgeIndex(index)
    }
}

impl<Ix: fmt::Debug> fmt::Debug for EdgeIndex<Ix> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "EdgeIndex({:?})", self.0)
    }
}

impl<Ix: fmt::Display> fmt::Display for EdgeIndex<Ix> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_node_index() {
        let n1 = NodeIndex::<usize>::new(1);
        let n2 = NodeIndex::<usize>::new(2);
        assert!(n1 < n2);
        assert!(n1 != n2);
        assert!(n1 == NodeIndex::new(1));
        assert!(n2 == NodeIndex::new(2));
        assert_eq!(n1.index(), 1);
        assert_eq!(n2.index(), 2);
    }

    #[test]
    fn test_edge_index() {
        let e1 = EdgeIndex::<usize>::new(1);
        let e2 = EdgeIndex::<usize>::new(2);
        assert!(e1 < e2);
        assert!(e1 != e2);
        assert!(e1 == EdgeIndex::new(1));
        assert!(e2 == EdgeIndex::new(2));
        assert_eq!(e1.index(), 1);
        assert_eq!(e2.index(), 2);
    }
}
