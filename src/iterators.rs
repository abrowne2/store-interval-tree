use std::{sync::Arc, vec::Vec};
use core::{cmp::Ord, fmt::Debug};
use crate::{interval::Interval, node::Node, SerializableRwLock};

/// A `find` query on the interval tree does not directly return references to the nodes in the tree, but
/// wraps the fields `interval` and `data` in an `Entry`.
#[derive(PartialEq, Debug)]
pub struct Entry<'a, T: Ord, V> {
    value: &'a SerializableRwLock<V>,
    interval: &'a Interval<T>,
}

impl<'a, T: Ord + 'a, V: 'a> Entry<'a, T, V> {
    /// Get a reference to the data for this entry
    #[must_use]
    pub fn value(&self) -> &'a SerializableRwLock<V> {
        self.value
    }

    /// Get a reference to the interval for this entry
    #[must_use]
    pub fn interval(&self) -> &'a Interval<T> {
        self.interval
    }
}

/// An `IntervalTreeMapIterator` is returned by `Intervaltree::find` and iterates over the entries
/// overlapping the query
#[derive(Debug)]
#[derive(rkyv::Archive, rkyv::Deserialize, rkyv::Serialize)]
#[archive(check_bytes)]
pub struct IntervalTreeMapIterator<'v, 'i, T: Ord + rkyv::Archive, V: rkyv::Archive> {
    pub(crate) nodes: Vec<&'v Node<T, V>>,
    pub(crate) interval: &'i Interval<T>,
}

impl<'v, 'i, T: Ord + rkyv::Archive, V: rkyv::Archive> Iterator for IntervalTreeMapIterator<'v, 'i, T, V> {
    type Item = Entry<'v, T, V>;

    fn next(&mut self) -> Option<Entry<'v, T, V>> {
        loop {
            let node_ref = match self.nodes.pop() {
                None => return None,
                Some(node) => node,
            };

            if node_ref.right_child.is_some() {
                self.nodes.push(node_ref.right_child.as_ref().unwrap());
            }
            if node_ref.left_child.is_some()
                && Node::<T, V>::is_ge(
                    &node_ref.left_child.as_ref().unwrap().get_max(),
                    &self.interval.get_low(),
                )
            {
                self.nodes.push(node_ref.left_child.as_ref().unwrap());
            }

            if Interval::overlaps(node_ref.interval(), self.interval) {
                return Some(Entry {
                    value: node_ref.value(),
                    interval: node_ref.interval(),
                });
            }
        }
    }
}

/// A `find_mut` query on the interval tree does not directly return references to the nodes in the tree, but
/// wraps the fields `interval` and `data` in an `EntryMut`. Only the data part can be mutably accessed
/// using the `data` method
#[derive(PartialEq, Debug)]
pub struct EntryMut<'a, T: Ord, V> {
    value: &'a mut SerializableRwLock<V>,
    interval: &'a Interval<T>,
}

impl<'a, T: Ord + 'a, V: 'a> EntryMut<'a, T, V> {
    /// Get a mutable reference to the data for this entry
    pub fn value(&'a mut self) -> &'a mut SerializableRwLock<V> {
        self.value
    }

    /// Get a reference to the interval for this entry
    #[must_use]
    pub fn interval(&self) -> &'a Interval<T> {
        self.interval
    }
}

/// An `IntervalTreeMapIteratorMut` is returned by `Intervaltree::find_mut` and iterates over the entries
/// overlapping the query allowing mutable access to the data `D`, not the `Interval`.
#[derive(Debug)]
#[derive(rkyv::Archive, rkyv::Deserialize, rkyv::Serialize)]
#[archive(check_bytes)]
pub struct IntervalTreeMapIteratorMut<'v, 'i, T: Ord + rkyv::Archive, V: rkyv::Archive> {
    pub(crate) nodes: Vec<&'v mut Node<T, V>>,
    pub(crate) interval: &'i Interval<T>,
}

impl<'v, 'i, T: Ord + rkyv::Archive, V: rkyv::Archive> Iterator for IntervalTreeMapIteratorMut<'v, 'i, T, V> {
    type Item = EntryMut<'v, T, V>;

    fn next(&mut self) -> Option<EntryMut<'v, T, V>> {
        loop {
            let node_ref = match self.nodes.pop() {
                None => return None,
                Some(node) => node,
            };

            let overlaps = Interval::overlaps(node_ref.interval(), self.interval);

            if node_ref.right_child.is_some() {
                self.nodes.push(node_ref.right_child.as_mut().unwrap());
            }
            if node_ref.left_child.is_some()
                && Node::<T, V>::is_ge(
                    &node_ref.left_child.as_ref().unwrap().get_max(),
                    &self.interval.get_low(),
                )
            {
                self.nodes.push(node_ref.left_child.as_mut().unwrap());
            }

            if overlaps {
                return Some(EntryMut {
                    value: Arc::get_mut(node_ref.value.as_mut().unwrap()).unwrap(),
                    interval: node_ref.interval.as_ref().unwrap(),
                });
            }
        }
    }
}

/// An `InOrderIterator` iterates over all intervals and values in the tree in-order
#[derive(Debug, rkyv::Archive, rkyv::Deserialize, rkyv::Serialize)]
#[archive(check_bytes)]
pub struct InOrderIterator<'v, T: Ord + rkyv::Archive, V: rkyv::Archive> {
    pub(crate) nodes: Vec<(&'v Node<T, V>, bool)>, // (node, visited)
}

impl<'v, T: Ord + rkyv::Archive, V: rkyv::Archive> Iterator for InOrderIterator<'v, T, V> {
    type Item = Entry<'v, T, V>;

    fn next(&mut self) -> Option<Entry<'v, T, V>> {
        while let Some((node, visited)) = self.nodes.pop() {
            if visited {
                // If we've visited this node before, return it and process right child
                if let Some(right) = &node.right_child {
                    self.nodes.push((right.as_ref(), false));
                }
                return Some(Entry {
                    value: node.value(),
                    interval: node.interval(),
                });
            } else {
                // Push back current node as visited
                self.nodes.push((node, true));

                // Process left subtree first
                if let Some(left) = &node.left_child {
                    self.nodes.push((left.as_ref(), false));
                }
            }
        }
        None
    }
}
