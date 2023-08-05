# graphed
`graphed` is a library that provides a simple way to create and manipulate graphs in your Rust project. Whether you're working on a data science project, building a recommendation system, or want to visualize your data more intuitively, `graphed` makes it easy to get started. 

## Installation
To use `graphed` in your project, you have to add the `graphed` crate to your `Cargo.toml` file. 

```toml
[dependencies]
graphed = "0.1.0"
```

## Usage
To create a graph with two nodes (Node 1 and Node 2) and an edge between them with a value of 1, you can do the following:

```rust
use graphed::graph::DiGraph;

let mut gr = DiGraph::<&str, usize>::new();
let idx_n1 = gr.add_node("Node 1");
let idx_n2 = gr.add_node("Node 2");

let _ = gr.add_edge(idx_n1, idx_n2, 1);
```

If you need a custom node or edge struct, e.g., for additional data, you can specify your structs and use them as the generic parameter of the Graph class. An example with a custom node (CustomNode) and a custom edge (CustomEdge) is shown below:
```rust
use graphed::graph::Graph;

pub struct CustomNode(usize);
pub struct CustomEdge(usize);

let mut gr = DiGraph::<CustomNode, CustomEdge>::new();
let idx_n1 = gr.add_node(CustomNode(1));
let idx_n2 = gr.add_node(CustomNode(2));

let _ = gr.add_edge(idx_n1, idx_n2, CustomEdge(123));
```

## Contributions
Contributions are welcome! Please open an issue or submit a pull request if you have any improvements to the library.