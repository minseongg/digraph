// TODO: Add tests for `find_sccs`, `paths_in_dag`.

use digraph::DiGraph;

const DAG_EDGES: &'static [(usize, usize)] = &[
    (5, 11),
    (7, 11),
    (7, 8),
    (3, 8),
    (3, 10),
    (11, 2),
    (11, 9),
    (11, 10),
    (8, 9),
];

fn basic() -> DiGraph<&'static str> {
    let mut digraph = DiGraph::new();

    digraph.add_pair_with_edge("src", "v1");
    digraph.add_pair_with_edge("v1", "v2");
    digraph.add_pair_with_edge("v2", "v3");
    digraph.add_pair_with_edge("v3", "v1");
    digraph.add_pair_with_edge("v2", "dst");

    digraph
}

fn triangle() -> DiGraph<usize> {
    // reference: https://en.wikipedia.org/wiki/File:Directed.svg
    let mut digraph = DiGraph::new();

    digraph.add_pair_with_edge(1, 2);
    digraph.add_pair_with_edge(2, 3);
    digraph.add_pair_with_edge(3, 1);

    digraph
}

fn directed_acyclic_graph() -> DiGraph<usize> {
    // reference: https://en.wikipedia.org/wiki/File:Directed_acyclic_graph_2.svg
    let mut digraph = DiGraph::new();

    for (u, v) in DAG_EDGES {
        digraph.add_pair_with_edge(*u, *v);
    }

    digraph
}

fn directed_acyclic_graph_rev() -> DiGraph<usize> {
    let mut digraph = DiGraph::new();

    for (u, v) in DAG_EDGES {
        digraph.add_pair_with_edge(*v, *u);
    }

    digraph
}

fn directed_acyclic_graph_sub() -> DiGraph<usize> {
    // reference: https://en.wikipedia.org/wiki/File:Directed_acyclic_graph_2.svg
    let mut digraph = DiGraph::new();

    digraph.add_pair_with_edge(5, 11);
    digraph.add_pair_with_edge(7, 11);
    digraph.add_pair_with_edge(11, 10);

    digraph
}

fn directed_acyclic_graph_sub_conn() -> DiGraph<usize> {
    // reference: https://en.wikipedia.org/wiki/File:Directed_acyclic_graph_2.svg
    let mut digraph = DiGraph::new();

    digraph.add_pair_with_edge(5, 11);
    digraph.add_pair_with_edge(7, 11);
    digraph.add_pair_with_edge(11, 10);
    digraph.add_pair_with_edge(5, 10);
    digraph.add_pair_with_edge(7, 10);

    digraph
}

fn directed_acyclic_graph_twice() -> DiGraph<usize> {
    let mut digraph = DiGraph::new();

    for (u, v) in DAG_EDGES {
        digraph.add_pair_with_edge(*u * 2, *v * 2);
    }

    digraph
}

#[test]
fn test_basic() {
    let digraph = basic();

    // tests `contains`
    assert!(digraph.contains(&"src"));
    assert!(!digraph.contains(&"v4"));

    // tests `get_vertices`
    assert_eq!(
        digraph.get_vertices(),
        ["src", "v1", "v2", "v3", "dst"].into_iter().collect()
    );

    // tests `get_edges`
    assert_eq!(digraph.get_edges(&"v1"), ["v2"].into_iter().collect());
    assert_eq!(
        digraph.get_edges(&"v2"),
        ["v3", "dst"].into_iter().collect()
    );

    // tests `outdegree`, `indegree`
    assert_eq!(digraph.outdegree(&"v1"), 1);
    assert_eq!(digraph.indegree(&"v1"), 2);
    assert_eq!(digraph.outdegree(&"dst"), 0);
    assert_eq!(digraph.indegree(&"dst"), 1);
    assert_eq!(digraph.outdegree(&"src"), 1);
    assert_eq!(digraph.indegree(&"src"), 0);

    // tests `find_sources`, `find_sinks`
    assert_eq!(digraph.find_sources(), ["src"].into_iter().collect());
    assert_eq!(digraph.find_sinks(), ["dst"].into_iter().collect());
}

#[test]
fn test_linearize() {
    let mut digraph = directed_acyclic_graph();

    // tests `linearize`
    let order = digraph.linearize();

    for v in order {
        assert_eq!(digraph.indegree(&v), 0);
        digraph.remove_vertex(&v);
    }

    assert_eq!(digraph.get_vertices().len(), 0);
}

#[test]
#[should_panic]
fn test_linearize_cyclic() {
    let digraph = triangle();

    // tests `linearize` with cyclic graph
    digraph.linearize();
}

#[test]
fn test_reachable_from() {
    let digraph = directed_acyclic_graph();

    // tests `reachable_from`
    assert_eq!(
        digraph.reachable_from(5),
        [11, 2, 9, 10].into_iter().collect()
    );
    assert_eq!(digraph.reachable_from(11), [2, 9, 10].into_iter().collect());
    assert_eq!(
        digraph.reachable_from(7),
        [11, 2, 8, 9, 10].into_iter().collect()
    );
    assert_eq!(digraph.reachable_from(3), [8, 9, 10].into_iter().collect());
}

#[test]
fn test_path() {
    let digraph = directed_acyclic_graph();

    // tests `path`.
    assert_eq!(digraph.path(5, 10), vec![5, 11, 10]);
    assert_eq!(digraph.path(3, 9), vec![3, 8, 9]);
}

#[test]
#[should_panic]
fn test_path_non_exist() {
    let digraph = directed_acyclic_graph();

    // tests `path` with non-exist path
    digraph.path(5, 8);
}

#[test]
fn test_reverse() {
    // tests `reverse`
    assert_eq!(
        directed_acyclic_graph().reverse(),
        directed_acyclic_graph_rev(),
    );
}

#[test]
fn test_subgraph() {
    // tests `subgraph`
    assert_eq!(
        directed_acyclic_graph().subgraph([5, 7, 11, 10].into_iter().collect()),
        directed_acyclic_graph_sub(),
    );
}

#[test]
fn test_simplify() {
    // tests `simplify`
    assert_eq!(
        directed_acyclic_graph().simplify([5, 7, 11, 10].into_iter().collect()),
        directed_acyclic_graph_sub_conn(),
    );
}

#[test]
fn test_transform_nodes() {
    // tests `transform_nodes`
    assert_eq!(
        directed_acyclic_graph().transform_nodes(|v| v * 2),
        directed_acyclic_graph_twice(),
    );
}
