struct Graph<T> {
    nodes: Vec<T>,
    edges: Vec<Vec<usize>>,
}

impl<T: Eq> Graph<T> {
    pub fn dependancies(&self, n: &T) -> Option<Vec<usize>> {
        let mut dependancies = vec![];
        let mut done = vec![false; self.nodes.len()];

        let i = self.find_index(n)?;
        let mut todo = vec![i]; // elements there are indices of elements in nodes
        done[i] = true;

        while let Some(i) = todo.pop() {
            for &j in &self.edges[i] {
                if !done[j] {
                    dependancies.push(j);
                    todo.push(j);
                    done[j] = true;
                }
            }
        }
        Some(dependancies)
    }

    pub fn find_index(&self, n: &T) -> Option<usize> {
        self.nodes.iter().position(|x| x == n)
    }

    pub fn dependency_list(&self) -> Vec<Vec<usize>> {
        self.nodes
            .iter()
            .map(|n| self.dependancies(n).unwrap())
            .collect()
    }
}
