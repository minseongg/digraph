//! Represents common behavior of all directed graphs.
//!
//! [`DiGraph.scala`](https://github.com/chipsalliance/firrtl/blob/v1.0.0/src/main/scala/firrtl/graph/DiGraph.scala)

#![feature(hash_drain_filter)]

use std::cmp::min;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone)]
struct StrongConnectFrame<T: Debug + Clone + Eq + Hash> {
    v: T,
    edge_iter: VecDeque<T>,
    child_call: Option<T>,
}

impl<T: Debug + Clone + Eq + Hash> StrongConnectFrame<T> {
    fn new(v: T, edge_iter: VecDeque<T>) -> Self {
        Self {
            v,
            edge_iter,
            child_call: None,
        }
    }
}

/// Represents a directed graph which allows loop but does not allow parallel edges.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct DiGraph<T: Debug + Clone + Eq + Hash> {
    edges: HashMap<T, HashSet<T>>,
}

impl<T: Debug + Clone + Eq + Hash> DiGraph<T> {
    /// Creates new digraph.
    pub fn new() -> Self {
        Self {
            edges: HashMap::new(),
        }
    }

    /// Checks whether the graph contains vertex v.
    pub fn contains(&self, v: &T) -> bool {
        self.edges.contains_key(v)
    }

    /// Returns all vertices in the graph.
    pub fn get_vertices(&self) -> HashSet<T> {
        self.edges.iter().map(|(k, _)| k).cloned().collect()
    }

    /// Returns all edges of a node.
    pub fn get_edges(&self, v: &T) -> HashSet<T> {
        self.edges.get(v).cloned().unwrap_or_default()
    }

    /// Returns number of edges start from a node.
    pub fn outdegree(&self, v: &T) -> usize {
        self.get_edges(v).len()
    }

    /// Returns number of edges end from a node.
    pub fn indegree(&self, v: &T) -> usize {
        let mut indegree = 0;
        for edges in self.edges.values() {
            if edges.contains(v) {
                indegree += 1;
            }
        }
        indegree
    }

    #[allow(missing_docs)]
    pub fn get_edge_map(&self) -> HashMap<T, HashSet<T>> {
        self.edges.clone()
    }

    /// Finds all sources in the graph.
    pub fn find_sources(&self) -> HashSet<T> {
        let mut vertices = self.get_vertices();
        for v in self.edges.values().into_iter().flatten() {
            vertices.remove(v);
        }
        vertices
    }

    /// Finds all sinks in the graph.
    pub fn find_sinks(&self) -> HashSet<T> {
        self.reverse().find_sources()
    }

    fn visit(
        &self,
        n: T,
        order: &mut Vec<T>,
        unmarked: &mut HashSet<T>,
        temp_marked: &mut HashSet<T>,
    ) {
        if temp_marked.contains(&n) {
            panic!("No valid linearization for cyclic graph");
        }
        if unmarked.contains(&n) {
            temp_marked.insert(n.clone());
            unmarked.remove(&n);
            for m in self.get_edges(&n) {
                self.visit(m, order, unmarked, temp_marked);
            }
            temp_marked.remove(&n);
            order.push(n);
        }
    }

    /// Linearizes (topologically sorts) a DAG.
    pub fn linearize(&self) -> Vec<T> {
        // permanently marked nodes are implicitly held in order
        let mut order = Vec::new();
        // invariant: no intersection between unmarked and temp_marked
        let mut unmarked = self.get_vertices();
        let mut temp_marked = HashSet::new();

        while !unmarked.is_empty() {
            self.visit(
                unmarked.iter().next().cloned().unwrap(),
                &mut order,
                &mut unmarked,
                &mut temp_marked,
            );
        }

        order.reverse();
        order
    }

    /// Performs breadth-first search on the directed graph.
    ///
    /// Returns a map from each visited node to its predecessor in the traversal.
    pub fn bfs(&self, root: T) -> HashMap<T, T> {
        let mut prev = HashMap::new();
        let mut queue = VecDeque::new();
        queue.push_back(root);
        while !queue.is_empty() {
            let u = queue.pop_front().unwrap();
            for v in self.get_edges(&u) {
                if !prev.contains_key(&v) {
                    prev.insert(v.clone(), u.clone());
                    queue.push_back(v);
                }
            }
        }
        prev
    }

    /// Finds the set of nodes reachable from a particular node.
    pub fn reachable_from(&self, root: T) -> HashSet<T> {
        self.bfs(root).keys().into_iter().cloned().collect()
    }

    /// Finds a path (if one exists) from one node to another.
    pub fn path(&self, start: T, end: T) -> Vec<T> {
        let mut node_path = vec![end];
        let prev = self.bfs(start.clone());

        while node_path.last().unwrap() != &start && prev.contains_key(node_path.last().unwrap()) {
            node_path.push(prev.get(node_path.last().unwrap()).unwrap().clone());
        }

        assert_eq!(node_path.last().unwrap(), &start, "Unreachable node");

        node_path.reverse();
        node_path
    }

    /// Finds the strongly connected components in the graph.
    ///
    /// Returns a vector of `Vec<T>`, each containing nodes of an SCC in traversal order.
    pub fn find_sccs(&self) -> Vec<Vec<T>> {
        let mut counter = 0;
        let mut stack = Vec::new();
        let mut onstack = HashSet::new();
        let mut indices = HashMap::new();
        let mut lowlinks = HashMap::new();
        let mut sccs = Vec::new();

        // # Note
        //
        // Recursive code is transformed to iterative code by representing call stack into an explicit
        // structure. Here, the stack data consists of the current vertex, its currently active edge,
        // and the position in the function. Because there is only one recursive call site, remembering
        // whether a child call was created on the last iteration where the current frame was active is
        // sufficient to track the position.
        let mut call_stack = Vec::<StrongConnectFrame<T>>::new();

        for node in self.get_vertices() {
            if indices.contains_key(&node) {
                continue;
            }

            call_stack.push(StrongConnectFrame::new(
                node.clone(),
                self.get_edges(&node).iter().cloned().collect(),
            ));

            while !call_stack.is_empty() {
                let frame = call_stack.last_mut().unwrap();
                let v = &frame.v;

                match &frame.child_call {
                    None => {
                        indices.insert(v.clone(), counter);
                        lowlinks.insert(v.clone(), counter);
                        counter += 1;
                        stack.push(v.clone());
                        onstack.insert(v.clone());
                    }
                    Some(w) => {
                        lowlinks.insert(
                            v.clone(),
                            min(*lowlinks.get(v).unwrap(), *lowlinks.get(w).unwrap()),
                        );
                    }
                }

                frame.child_call = None;

                let mut new_frames = Vec::new();
                while !frame.edge_iter.is_empty() && frame.child_call.is_none() {
                    let w = frame.edge_iter.pop_front().unwrap();
                    if !indices.contains_key(&w) {
                        frame.child_call = Some(w.clone());
                        new_frames.push(StrongConnectFrame::new(
                            w.clone(),
                            self.get_edges(&w).into_iter().collect(),
                        ));
                    } else if onstack.contains(&w) {
                        lowlinks.insert(
                            v.clone(),
                            min(*lowlinks.get(v).unwrap(), *indices.get(&w).unwrap()),
                        );
                    }
                }

                if frame.child_call.is_none() {
                    if lowlinks.get(v) == indices.get(v) {
                        let mut scc = Vec::new();
                        loop {
                            let w = stack.pop().unwrap();
                            onstack.remove(&w);
                            scc.push(w);

                            if scc.last() == Some(v) {
                                break;
                            }
                        }
                        sccs.push(scc);
                    }
                    call_stack.pop();
                } else {
                    for new_frame in new_frames {
                        call_stack.push(new_frame);
                    }
                }
            }
        }

        sccs
    }

    /// Finds all paths starting at a particular node in a DAG.
    ///
    /// # Note
    ///
    /// This is an exponential time algorithm (as any algorithm must be for this problem), but is
    /// useful for flattening circuit graph hierarchies. Each path is represented by a `Vec<T>` of
    /// nodes in a traversal order.
    pub fn paths_in_dag(&self, start: T) -> HashMap<T, Vec<Vec<T>>> {
        // paths(v) holds the set of paths from start to v
        let mut paths = HashMap::new();
        let mut queue = VecDeque::new();
        let reachable = self.reachable_from(start.clone());

        let add_binding = |n: T, p: Vec<T>, paths: &mut HashMap<T, HashSet<Vec<T>>>| {
            (*paths.entry(n).or_default()).insert(p);
        };

        add_binding(start.clone(), vec![start.clone()], &mut paths);
        queue.push_back(start);

        for n in self.linearize().iter().filter(|n| reachable.contains(n)) {
            queue.push_back(n.clone());
        }

        while !queue.is_empty() {
            let current = queue.pop_front().unwrap();
            for v in self.get_edges(&current) {
                let ps = paths.get(&current).unwrap().clone();
                for mut p in ps {
                    p.push(v.clone());
                    add_binding(v.clone(), p, &mut paths);
                }
            }
        }

        paths
            .iter()
            .map(|(k, v)| (k.clone(), v.iter().cloned().collect()))
            .collect()
    }

    /// Returns a graph with all edges reversed.
    pub fn reverse(&self) -> Self {
        let mut digraph = DiGraph::new();
        for u in self.edges.keys() {
            digraph.add_vertex(u.clone());
        }
        for (u, edges) in &self.edges {
            for v in edges {
                digraph.add_edge(v.clone(), u.clone());
            }
        }
        digraph
    }

    fn filter_edges(&self, vprime: HashSet<T>) -> HashMap<T, HashSet<T>> {
        let filter_node_set =
            |mut s: HashSet<T>| -> HashSet<T> { s.drain_filter(|k| vprime.contains(k)).collect() };

        let filter_adj_lists = |m: HashMap<T, HashSet<T>>| -> HashMap<T, HashSet<T>> {
            m.iter()
                .map(|(k, v)| (k.clone(), filter_node_set(v.clone())))
                .collect()
        };

        let eprime = self
            .edges
            .clone()
            .drain_filter(|k, _| vprime.contains(k))
            .collect();

        filter_adj_lists(eprime)
    }

    /// Returns a graph with only a subset of the nodes.
    ///
    /// Any edge including a deleted node will be deleted.
    pub fn subgraph(&self, vprime: HashSet<T>) -> Self {
        assert!(vprime.is_subset(&self.edges.keys().into_iter().cloned().collect()));
        Self {
            edges: self.filter_edges(vprime),
        }
    }

    /// Returns a simplified connectivity graph with only a subset of the nodes.
    ///
    /// Any path between two non-deleted nodes (u, v) in the original graph will be transformed into
    /// an edge (u, v).
    pub fn simplify(&self, vprime: HashSet<T>) -> Self {
        assert!(vprime.is_subset(&self.edges.keys().into_iter().cloned().collect()));
        let path_edges = vprime
            .iter()
            .map(|v| {
                let mut vprime = vprime.clone();
                vprime.remove(v);

                (
                    v.clone(),
                    self.reachable_from(v.clone())
                        .intersection(&vprime)
                        .into_iter()
                        .cloned()
                        .collect(),
                )
            })
            .collect();
        Self { edges: path_edges }
    }

    /// Returns a graph with all the nodes of the current graph transformed by a function.
    /// Edge connectivity will be the same as the current graph.
    pub fn transform_nodes<Q, F: Fn(T) -> Q>(&self, f: F) -> DiGraph<Q>
    where
        Q: Debug + Clone + Eq + Hash,
    {
        let eprime = self
            .edges
            .iter()
            .map(|(k, v)| (f(k.clone()), v.iter().map(|n| f(n.clone())).collect()))
            .collect();
        DiGraph { edges: eprime }
    }

    /// Adds vertex v to the graph.
    ///
    /// Returns the added vertex.
    pub fn add_vertex(&mut self, v: T) -> T {
        self.edges.entry(v.clone()).or_default();
        v
    }

    /// Removes vertex v from the graph.
    pub fn remove_vertex(&mut self, v: &T) {
        self.edges.remove(v);
        for edges in self.edges.values_mut() {
            edges.remove(v);
        }
    }

    /// Adds edge (u, v) to the graph.
    ///
    /// Assumes that u and v are in the graph.
    pub fn add_edge(&mut self, u: T, v: T) {
        assert!(self.contains(&u));
        assert!(self.contains(&v));
        self.edges.entry(u).and_modify(|nbrs| {
            nbrs.insert(v);
        });
    }

    /// Removes edge (u, v) from the graph.
    ///
    /// Assumes that u and v are in the graph.
    pub fn remove_edge(&mut self, u: &T, v: &T) {
        assert!(self.contains(u));
        assert!(self.contains(v));
        self.edges.entry(u.clone()).and_modify(|nbrs| {
            nbrs.remove(v);
        });
    }

    /// Adds edge (u, v) to the graph, adding u and/or v if they are not already in the graph.
    pub fn add_pair_with_edge(&mut self, u: T, v: T) {
        self.edges.entry(v.clone()).or_default();
        (*self.edges.entry(u).or_default()).insert(v);
    }

    /// Adds edge (u, v) to the graph if and only if both u and v are in the graph prior to calling
    /// `add_edge_if_valid`.
    pub fn add_edge_if_valid(&mut self, u: T, v: T) -> bool {
        let valid = self.contains(&u) && self.contains(&v);
        if valid {
            self.edges.entry(u).and_modify(|nbrs| {
                nbrs.insert(v);
            });
        }
        valid
    }
}
