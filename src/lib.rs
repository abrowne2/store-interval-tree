#![warn(clippy::cargo)]
#![recursion_limit = "1024"]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(clippy::all)]
#![warn(
    missing_debug_implementations,
    trivial_numeric_casts,
    unused_extern_crates,
    unused_import_braces,
    unused_qualifications,
    unused_must_use
)]
#![warn(clippy::pedantic)]
#![allow(clippy::comparison_chain)]
// TODO: check https://rust-lang.github.io/rust-clippy/master/index.html#derive_hash_xor_eq
#![allow(clippy::derive_hash_xor_eq)]
#![allow(clippy::missing_panics_doc)]

use std::{sync::Arc, vec::Vec, boxed::Box};
use std::collections::HashMap;
use core::cmp::Ord;
use core::fmt::Debug;
mod interval;
pub mod range;
use rkyv::*;
use range::Bound;
pub use interval::Interval;

mod node;
use node::Node;

mod iterators;
pub use iterators::{Entry, EntryMut, IntervalTreeMapIterator, IntervalTreeMapIteratorMut};
use ser::serializers::AllocScratch;
use serde::{de, Deserialize, Serialize};

#[derive(Clone, Default, PartialEq, Deserialize, Serialize, Debug, Hash, Eq, PartialOrd, Ord)]
#[derive(rkyv::Archive, rkyv::Deserialize, rkyv::Serialize)]
#[archive_attr(derive(Hash, Eq, PartialEq, PartialOrd, Ord))]
pub struct IntervalValueKey(String);

impl IntervalValueKey {
    pub fn new(key: String) -> IntervalValueKey {
        IntervalValueKey(key)
    }

    pub fn from(key: &str) -> IntervalValueKey {
        IntervalValueKey(key.to_string())
    }
}

impl std::fmt::Display for IntervalValueKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// An interval tree map is a tree data structure to hold intervals.
/// It also allows for storing associated values with each interval.
/// And for O(1) access to the associated value in a node by a specific identifier.
/// Specifically, it allows one to efficiently find all intervals that overlap with any given interval or point.
///
/// This data structure is backed by a `store_interval_tree:IntervalTreeMap`
///
/// # Examples
/// ```
/// use store_interval_tree::IntervalTreeMap;
/// use store_interval_tree::Interval;
/// use std::ops::Bound::*;
///
/// // initialize an interval tree with end points of type usize
/// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
///
/// // insert interval into the tree
/// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
/// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
/// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
/// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
/// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
/// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
/// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
/// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
/// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
///
/// let interval1 = Interval::new(Excluded(23), Included(26));
///
/// // interval (25, 30] is overlapped with interval (23,26]
/// assert!(interval_tree.find_overlap(&interval1).unwrap() == Interval::new(Excluded(25), Included(30)));
///
/// // there is no interval in the tree that has interval with (10,15)
/// assert!(interval_tree.find_overlap(&Interval::new(Excluded(10), Excluded(15))).is_none());
///
/// // find all overlaps with an interval
/// let interval = Interval::new(Included(8), Included(26));
/// // intervals are: (8,9], [6,10],(19,20], [16,21), (15,23), [17,19), (25,30], [26,26]
/// let intervals = interval_tree.find_overlaps(&interval);
///
/// // delete interval
/// let interval = Interval::new(Included(15), Included(18));
/// let overlapped_interval = interval_tree.find_overlap(&interval).unwrap();
/// interval_tree.delete(&overlapped_interval);
///
/// // find all intervals between two intervals/points
/// let low = Interval::point(14);
/// let high = Interval::point(24);
/// // intervals are: (15,23), [16,21), [17,19), (19,20]
/// let intervals = interval_tree.intervals_between(&low, &high);
/// ```
#[derive(Clone, Default, PartialEq, Deserialize, Serialize)]
#[derive(rkyv::Archive, rkyv::Deserialize, rkyv::Serialize)]
#[archive(check_bytes)]
#[archive(bound(serialize = "T: rkyv::Serialize<__S>, V: rkyv::Serialize<__S>, __S: rkyv::ser::Serializer + rkyv::ser::SharedSerializeRegistry"))]
#[archive(bound(deserialize = "T: rkyv::Archive, V: rkyv::Archive, <T as rkyv::Archive>::Archived: rkyv::Deserialize<T, __D>, <V as rkyv::Archive>::Archived: rkyv::Deserialize<V, __D>, __D: rkyv::de::SharedDeserializeRegistry"))]
pub struct IntervalTreeMap<
    T: Ord + rkyv::Archive + rkyv::Serialize<rkyv::ser::serializers::CompositeSerializer<rkyv::ser::serializers::AlignedSerializer<AlignedVec>, AllocScratch>> + 'static,
    V: rkyv::Archive + rkyv::Serialize<rkyv::ser::serializers::CompositeSerializer<rkyv::ser::serializers::AlignedSerializer<AlignedVec>, AllocScratch>> + 'static,
> {
    #[omit_bounds]
    root: Option<Box<Node<T, V>>>,
    identifier_map: HashMap<IntervalValueKey, Arc<V>>, // Raw pointer to value stored in Node
}

impl<
T: Ord + rkyv::Archive + rkyv::Serialize<rkyv::ser::serializers::CompositeSerializer<rkyv::ser::serializers::AlignedSerializer<AlignedVec>, AllocScratch>> + 'static,
V: rkyv::Archive + rkyv::Serialize<rkyv::ser::serializers::CompositeSerializer<rkyv::ser::serializers::AlignedSerializer<AlignedVec>, AllocScratch>> + 'static,
> IntervalTreeMap<T, V> {
    /// Initialize an interval tree with end points of type usize
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    ///
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    /// ```
    #[must_use]
    pub fn new() -> IntervalTreeMap<T, V> {
        IntervalTreeMap { root: None, identifier_map: HashMap::new() }
    }

    /// Returns true if there are no intervals in the tree, false otherwise
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// Returns total number of intervals in the tree
    #[must_use]
    pub fn size(&self) -> usize {
        Node::size(&self.root)
    }

    /// Returns height of the tree
    #[must_use]
    pub fn height(&self) -> i64 {
        Node::height(&self.root)
    }

    /// Removes all intervals from the tree but keeps the allocated capacity
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// 
    /// interval_tree.clear();
    /// assert!(interval_tree.is_empty());
    /// ```
    pub fn clear(&mut self) {
        // Setting the root node to None will trigger a GC of the tree
        self.root = None;
        self.identifier_map.clear(); // Clears contents but preserves capacity
    }


    /// Find overlapping intervals in the tree and returns an
    /// `IntervalTreeMapIterator` that allows access to the stored value
    ///
    /// # Arguments
    /// * `interval`: interval to be searched for any overlaps
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    ///
    /// // insert interval into the tree
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// let interval1 = Interval::new(Excluded(23), Included(26));
    ///
    /// // interval (25, 30] is overlapped with interval (23,26]
    /// assert!(interval_tree.find_overlap(&interval1).unwrap() == Interval::new(Excluded(25), Included(30)));
    ///
    /// // there is no interval in the tree that has interval with (10,15)
    /// assert!(interval_tree.find_overlap(&Interval::new(Excluded(10), Excluded(15))).is_none());
    /// ```
    #[must_use]
    pub fn query<'a, 'v, 'i>(
        &'a self,
        interval: &'i Interval<T>,
    ) -> IntervalTreeMapIterator<'v, 'i, T, V>
    where
        'a: 'v,
        'a: 'i,
    {
        if let Some(ref n) = self.root {
            IntervalTreeMapIterator {
                nodes: vec![n],
                interval,
            }
        } else {
            let nodes = vec![];
            IntervalTreeMapIterator { nodes, interval }
        }
    }

    /// Find overlapping intervals in the tree and returns an
    /// `IntervalTreeMapIteratorMut` that allows mutable access to the stored value
    ///
    /// # Arguments
    /// * `interval`: interval to be searched for any overlaps
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    ///
    /// // insert interval into the tree
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// let interval1 = Interval::new(Excluded(23), Included(26));
    ///
    /// // interval (25, 30] is overlapped with interval (23,26]
    /// assert!(interval_tree.find_overlap(&interval1).unwrap() == Interval::new(Excluded(25), Included(30)));
    ///
    /// // there is no interval in the tree that has interval with (10,15)
    /// assert!(interval_tree.find_overlap(&Interval::new(Excluded(10), Excluded(15))).is_none());
    /// ```
    pub fn query_mut<'a, 'v, 'i>(
        &'a mut self,
        interval: &'i Interval<T>,
    ) -> IntervalTreeMapIteratorMut<'v, 'i, T, V>
    where
        'a: 'v,
        'a: 'i,
    {
        if let Some(ref mut n) = self.root {
            IntervalTreeMapIteratorMut {
                nodes: vec![n],
                interval,
            }
        } else {
            let nodes = vec![];
            IntervalTreeMapIteratorMut { nodes, interval }
        }
    }

    /// Returns true if there exists an interval in the tree that overlaps with specified `interval`
    ///
    /// # Arguments
    /// * `interval`: interval to be searched for any overlaps
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    ///
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    ///
    /// assert!(!interval_tree.overlaps(&Interval::new(Included(4), Excluded(6))));
    /// assert!(interval_tree.overlaps(&Interval::new(Included(4), Included(6))));
    /// ```
    #[must_use]
    pub fn overlaps(&self, interval: &Interval<T>) -> bool {
        self.find_overlap(interval).is_some()
    }

    /// Returns first interval that overlaps with specified `interval`
    ///
    /// # Arguments:
    /// * `interval`: interval to be searched for any overlaps
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// // initialize an interval tree with end points of type usize
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    ///
    /// // insert interval into the tree
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// let interval1 = Interval::new(Excluded(23), Included(26));
    ///
    /// // interval (25, 30] is overlapped with interval (23,26]
    /// assert!(interval_tree.find_overlap(&interval1).unwrap() == Interval::new(Excluded(25), Included(30)));
    ///
    /// // there is no interval in the tree that has interval with (10,15)
    /// assert!(interval_tree.find_overlap(&Interval::new(Excluded(10), Excluded(15))).is_none());
    /// ```
    #[must_use]
    pub fn find_overlap(&self, interval: &Interval<T>) -> Option<Interval<T>> {
        IntervalTreeMap::_find_overlap(&self.root, interval)
    }

    pub fn get_node_value_by_key_mut(&mut self, key: IntervalValueKey) -> Option<&mut Arc<V>> {
        self.identifier_map.get_mut(&key)
    }

    pub fn get_node_value_by_key(&self, key: IntervalValueKey) -> Option<&Arc<V>> {
        self.identifier_map.get(&key)
    }

    fn _find_overlap(
        node: &Option<Box<Node<T, V>>>,
        interval: &Interval<T>,
    ) -> Option<Interval<T>> {
        if node.is_none() {
            return None;
        }
        let mut current = node;
        while current.is_some() {
            let node_ref = current.as_ref().unwrap();
            if Interval::overlaps(node_ref.interval(), interval) {
                break;
            }

            if node_ref.left_child.is_some()
                && Node::<T, V>::is_ge(
                    &node_ref.left_child.as_ref().unwrap().get_max(),
                    &interval.get_low(),
                )
            {
                current = &node_ref.left_child;
            } else {
                current = &node_ref.right_child;
            }
        }

        if current.is_none() {
            None
        } else {
            Some(current.as_ref().unwrap().interval().duplicate())
        }
    }

    /// Returns all intervals that overlap with the specified `interval`
    ///
    /// # Arguments
    /// * `interval`: interval to be searched for any overlaps
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// // initialize an interval tree with end points of type usize
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    ///
    /// // insert interval into the tree
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// // find all overlaps with an interval
    /// let interval = Interval::new(Included(8), Included(26));
    /// // intervals are: (8,9], [6,10],(19,20], [16,21), (15,23), [17,19), (25,30], [26,26]
    /// let intervals = interval_tree.find_overlaps(&interval);
    /// ```
    #[must_use]
    pub fn find_overlaps(&self, interval: &Interval<T>) -> Vec<Interval<T>> {
        let mut overlaps = Vec::<Interval<T>>::new();

        IntervalTreeMap::_find_overlaps(&self.root, interval, &mut overlaps);

        overlaps
    }

    fn _find_overlaps(
        node: &Option<Box<Node<T, V>>>,
        interval: &Interval<T>,
        overlaps: &mut Vec<Interval<T>>,
    ) {
        if node.is_none() {
            return;
        }
        let node_ref = node.as_ref().unwrap();
        if Interval::overlaps(node_ref.interval(), interval) {
            overlaps.push(node_ref.interval().duplicate());
        }

        if node_ref.left_child.is_some()
            && Node::<T, V>::is_ge(
                &node_ref.left_child.as_ref().unwrap().get_max(),
                &interval.get_low(),
            )
        {
            IntervalTreeMap::_find_overlaps(&node_ref.left_child, interval, overlaps);
        }
        IntervalTreeMap::_find_overlaps(&node_ref.right_child, interval, overlaps);
    }

    /// Find first interval that overlaps and matches the identifier, along with its associated value
    pub fn find_overlap_with_identifier(
        &self,
        interval: &Interval<T>,
        identifier: &IntervalValueKey,
    ) -> Option<(Interval<T>, &V)> {
        Self::_find_overlap_with_identifier(&self.root, interval, identifier)
    }

    fn _find_overlap_with_identifier<'a>(
        node: &'a Option<Box<Node<T, V>>>,
        interval: &Interval<T>,
        identifier: &IntervalValueKey,
    ) -> Option<(Interval<T>, &'a V)> {
        if node.is_none() {
            return None;
        }
        
        let mut current = node;
        while let Some(node_ref) = current {
            // Early pruning: if the subtree doesn't contain this identifier at all
            if !node_ref.subtree_identifiers.contains(identifier) {
                return None;
            }

            if Interval::overlaps(node_ref.interval(), interval) 
               && node_ref.identifier.as_ref().unwrap() == identifier {
                return Some((node_ref.interval().duplicate(), node_ref.value()));
            }

            // Choose subtree to explore
            // If the left child is not empty and the max of the left child is greater than or equal to the low of the interval,
            // Only go left if that subtree contains our identifier
            if node_ref.left_child.is_some()
                && Node::<T, V>::is_ge(
                    &node_ref.left_child.as_ref().unwrap().get_max(),
                    &interval.get_low(),
                )
                // Only go left if that subtree contains our identifier
                && node_ref.left_child.as_ref().unwrap().subtree_identifiers.contains(identifier)
            {
                current = &node_ref.left_child;
            } else {
                current = &node_ref.right_child;
            }
        }

        None
    }

    /// Inserts an interval in the tree. if interval already exists, `interval` will be ignored
    ///
    /// # Arguments
    /// * `interval`: interval to be inserted in the tree
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// // initialize an interval tree with end points of type usize
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    ///
    /// // insert interval into the tree
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    /// ```
    pub fn insert(&mut self, interval: Interval<T>, value: V, identifier: IntervalValueKey, value_key: IntervalValueKey) {
        let max = interval.get_high();

        let value_with_shared_pointer = Arc::new(value);

        if !self.identifier_map.contains_key(&value_key) {
            self.identifier_map.insert(value_key.clone(), value_with_shared_pointer.clone());
        }

        self.root = Some(IntervalTreeMap::_insert(
            self.root.take(),
            interval,
            value_with_shared_pointer,
            identifier,
            max,
            value_key,
        ));
    }

    fn _insert(
        node: Option<Box<Node<T, V>>>,
        interval: Interval<T>,
        value_with_shared_pointer: Arc<V>,
        identifier: IntervalValueKey,
        max: Arc<Bound<T>>,
        value_key: IntervalValueKey,
    ) -> Box<Node<T, V>> {
        if node.is_none() {
            return Box::new(Node::init(
                interval,
                value_with_shared_pointer,
                max,
                identifier,
                0,
                1,
                value_key,
            ));
        }

        let mut node_ref = node.unwrap();


        if interval < *node_ref.interval() {
            node_ref.left_child = Some(IntervalTreeMap::_insert(
                node_ref.left_child,
                interval,
                value_with_shared_pointer,
                identifier,
                max,
                value_key,
            ));
        } else if interval > *node_ref.interval() {
            node_ref.right_child = Some(IntervalTreeMap::_insert(
                node_ref.right_child,
                interval,
                value_with_shared_pointer,
                identifier,
                max,
                value_key,
            ));
        } else {
            return node_ref;
        }

        node_ref.update_height();
        node_ref.update_size();
        node_ref.update_max();
        node_ref.update_identifiers();
        IntervalTreeMap::balance(node_ref)
    }

    fn balance(mut node: Box<Node<T, V>>) -> Box<Node<T, V>> {
        if Node::balance_factor(&node) < -1 {
            if Node::balance_factor(node.right_child.as_ref().unwrap()) > 0 {
                node.right_child = Some(IntervalTreeMap::rotate_right(node.right_child.unwrap()));
            }
            node = IntervalTreeMap::rotate_left(node);
        } else if Node::balance_factor(&node) > 1 {
            if Node::balance_factor(node.left_child.as_ref().unwrap()) < 0 {
                node.left_child = Some(IntervalTreeMap::rotate_left(node.left_child.unwrap()));
            }
            node = IntervalTreeMap::rotate_right(node);
        }
        node
    }

    fn rotate_right(mut node: Box<Node<T, V>>) -> Box<Node<T, V>> {
        let mut y = node.left_child.unwrap();
        node.left_child = y.right_child;
        y.size = node.size;
        node.update_height();
        node.update_size();
        node.update_max();
        node.update_identifiers();
        y.right_child = Some(node);
        y.update_height();
        y.update_max();
        y.update_identifiers();
        y
    }

    fn rotate_left(mut node: Box<Node<T, V>>) -> Box<Node<T, V>> {
        let mut y = node.right_child.unwrap();
        node.right_child = y.left_child;
        y.size = node.size;

        node.update_height();
        node.update_size();
        node.update_max();
        node.update_identifiers();
        y.left_child = Some(node);
        y.update_height();
        y.update_max();
        y.update_identifiers();
        y
    }

    /// Delete the specified `interval` if found
    ///
    /// # Arguments
    /// * `interval`: interval to be deleted
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// // initialize an interval tree with end points of type usize
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    ///
    /// // insert interval into the tree
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// // delete interval
    /// let interval = Interval::new(Included(15), Included(18));
    /// let overlapped_interval = interval_tree.find_overlap(&interval).unwrap();
    /// interval_tree.delete(&overlapped_interval);
    /// ```
    pub fn delete(&mut self, interval: &Interval<T>) {
        if !self.is_empty() {
            self.root = IntervalTreeMap::_delete(self.root.take(), interval);
        }
    }

    fn _delete(node: Option<Box<Node<T, V>>>, interval: &Interval<T>) -> Option<Box<Node<T, V>>> {
        match node {
            None => None,
            Some(mut node) => {                
                if *interval < *node.interval() {
                    node.left_child = IntervalTreeMap::_delete(node.left_child.take(), interval);
                } else if *interval > *node.interval() {
                    node.right_child = IntervalTreeMap::_delete(node.right_child.take(), interval);
                } else if node.left_child.is_none() {
                    return node.right_child;
                } else if node.right_child.is_none() {
                    return node.left_child;
                } else {
                    let mut y = node;
                    node = IntervalTreeMap::_min(&mut y.right_child);
                    node.right_child = IntervalTreeMap::_delete_min(y.right_child.unwrap());
                    node.left_child = y.left_child;
                }

                node.update_height();
                node.update_size();
                node.update_max();
                node.update_identifiers();

                Some(IntervalTreeMap::balance(node))
            }
        }
    }
    fn _min(node: &mut Option<Box<Node<T, V>>>) -> Box<Node<T, V>> {
        match node {
            Some(node) => {
                if node.left_child.is_none() {
                    Box::new(Node::init(
                        node.get_interval(),
                        node.get_value(),
                        node.get_max(),
                        node.get_identifier(),
                        0,
                        1,
                        node.value_key().clone(),
                    ))
                } else {
                    IntervalTreeMap::_min(&mut node.left_child)
                }
            }
            None => panic!("Called min on None node"),
        }
    }

    /// Deletes minimum interval in the tree
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    ///
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Excluded(5), Included(8)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// interval_tree.delete_min();
    /// interval_tree.delete_min();
    ///
    /// assert!(interval_tree.find_overlap(&Interval::new(Included(1), Excluded(6))).is_none());
    /// ```
    pub fn delete_min(&mut self) {
        if !self.is_empty() {
            self.root = IntervalTreeMap::_delete_min(self.root.take().unwrap());
        }
    }

    fn _delete_min(mut node: Box<Node<T, V>>) -> Option<Box<Node<T, V>>> {
        if node.left_child.is_none() {
            return node.right_child.take();
        }

        node.left_child = IntervalTreeMap::_delete_min(node.left_child.unwrap());

        node.update_height();
        node.update_size();
        node.update_max();
        node.update_identifiers();

        Some(IntervalTreeMap::balance(node))
    }

    /// Deletes maximum interval in the tree
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    ///
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Excluded(5), Included(8)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// interval_tree.delete_max();
    /// interval_tree.delete_max();
    ///
    /// assert!(interval_tree.find_overlap(&Interval::new(Included(25), Excluded(30))).is_none());
    pub fn delete_max(&mut self) {
        if !self.is_empty() {
            self.root = IntervalTreeMap::_delete_max(self.root.take().unwrap());
        }
    }

    fn _delete_max(mut node: Box<Node<T, V>>) -> Option<Box<Node<T, V>>> {
        if node.right_child.is_none() {
            return node.left_child.take();
        }

        node.right_child = IntervalTreeMap::_delete_max(node.right_child.unwrap());

        node.update_height();
        node.update_size();
        node.update_max();
        node.update_identifiers();
        Some(IntervalTreeMap::balance(node))
    }

    /// Returns the kth smallest interval
    ///
    /// # Arguments
    /// * `k`: the order statistic
    ///
    /// # Panics
    /// * panics if k is not in range: 0 <= k <= size - 1
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    ///
    /// interval_tree.insert(Interval::new(Excluded(0), Included(1)), ());
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// assert!(format!("{}", interval_tree.select(0).unwrap()) == String::from("[0,3)"));
    /// assert!(format!("{}", interval_tree.select(1).unwrap()) == String::from("(0,1]"));
    /// assert!(format!("{}", interval_tree.select(2).unwrap()) == String::from("[6,10]"));
    /// assert!(format!("{}", interval_tree.select(3).unwrap()) == String::from("(8,9]"));
    /// ```
    #[must_use]
    pub fn select(&self, k: usize) -> Option<Interval<T>> {
        assert!(k <= self.size(), "K must be in range 0 <= k <= size - 1");
        IntervalTreeMap::_select(&self.root, k)
    }

    fn _select(node: &Option<Box<Node<T, V>>>, k: usize) -> Option<Interval<T>> {
        if node.is_none() {
            return None;
        }
        let node_ref = node.as_ref().unwrap();

        let t = Node::size(&node_ref.left_child);
        if t > k {
            IntervalTreeMap::_select(&node_ref.left_child, k)
        } else if t < k {
            IntervalTreeMap::_select(&node_ref.right_child, k - t - 1)
        } else {
            return Some(node_ref.interval().duplicate());
        }
    }

    /// Returns minimum interval in the tree
    #[must_use]
    pub fn min(&self) -> Option<Interval<T>> {
        self.select(0)
    }

    /// Returns maximum interval in the tree
    #[must_use]
    pub fn max(&self) -> Option<Interval<T>> {
        self.select(self.size() - 1)
    }

    /// Returns all intervals between two intervals/points
    ///
    /// # Arguments
    /// * `low_bound`: lowest interval of the range
    /// * `high_bound`: highest interval of the range
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    ///
    /// interval_tree.insert(Interval::new(Excluded(0), Included(1)), ());
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// let low = Interval::new(Included(14), Included(14));
    /// let high = Interval::new(Included(24), Included(24));
    /// let intervals = interval_tree.intervals_between(&low, &high);
    ///
    /// let accept = String::from("(15,23)[16,21)[17,19)(19,20]");
    ///
    /// let mut result = String::from("");
    /// for interval in intervals {
    ///     result.push_str(&format!("{}", interval))
    /// }
    ///
    /// assert_eq!(result, accept);
    /// ```
    #[must_use]
    pub fn intervals_between(
        &self,
        low_bound: &Interval<T>,
        high_bound: &Interval<T>,
    ) -> Vec<&Interval<T>> {
        let mut intervals: Vec<&Interval<T>> = Vec::new();

        IntervalTreeMap::_intervals_between(&self.root, low_bound, high_bound, &mut intervals);

        intervals
    }

    fn _intervals_between<'a>(
        node: &'a Option<Box<Node<T, V>>>,
        low_bound: &Interval<T>,
        high_bound: &Interval<T>,
        intervals: &mut Vec<&'a Interval<T>>,
    ) {
        if node.is_none() {
            return;
        }

        let node_ref = node.as_ref().unwrap();
        if *low_bound < *node_ref.interval() {
            IntervalTreeMap::_intervals_between(
                &node_ref.left_child,
                low_bound,
                high_bound,
                intervals,
            );
        }
        if *low_bound <= *node_ref.interval() && *node_ref.interval() <= *high_bound {
            intervals.push(node_ref.interval());
        }
        if *high_bound > *node_ref.interval() {
            IntervalTreeMap::_intervals_between(
                &node_ref.right_child,
                low_bound,
                high_bound,
                intervals,
            );
        }
    }

    /// Returns all intervals in the tree following an in-order traversal.
    /// Therefore intervals are sorted from smallest to largest
    #[must_use]
    pub fn intervals(&self) -> Vec<Interval<T>> {
        let mut intervals: Vec<Interval<T>> = Vec::new();

        IntervalTreeMap::_intervals_in_order(&self.root, &mut intervals);

        intervals
    }

    fn _intervals_in_order(node: &Option<Box<Node<T, V>>>, intervals: &mut Vec<Interval<T>>) {
        if node.is_none() {
            return;
        }

        let node_ref = node.as_ref().unwrap();
        IntervalTreeMap::_intervals_in_order(&node_ref.left_child, intervals);
        intervals.push(node_ref.interval().duplicate());
        IntervalTreeMap::_intervals_in_order(&node_ref.right_child, intervals);
    }

    /// Returns the number of intervals in the tree less than `interval`
    ///
    /// # Arguments
    /// * `interval`: interval to be searched for
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    ///
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Excluded(5), Included(8)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// assert_eq!(interval_tree.rank(&Interval::point(5)), 1);
    /// ```
    #[must_use]
    pub fn rank(&self, interval: &Interval<T>) -> usize {
        IntervalTreeMap::_rank(&self.root, interval)
    }
    fn _rank(node: &Option<Box<Node<T, V>>>, interval: &Interval<T>) -> usize {
        if node.is_none() {
            return 0;
        }
        let node_ref = node.as_ref().unwrap();
        if *interval < *node_ref.interval() {
            IntervalTreeMap::_rank(&node_ref.left_child, interval)
        } else if *interval >= *node_ref.interval() {
            1 + Node::size(&node_ref.left_child)
                + IntervalTreeMap::_rank(&node_ref.right_child, interval)
        } else {
            Node::size(&node_ref.left_child)
        }
    }

    /// Returns the number of intervals in the tree between `low_bound` and `high_bound`
    ///
    /// # Arguments
    /// * `low_bound`: lowest interval of the range
    /// * `high_bound`: highest interval of the range
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTreeMap;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
    ///
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Excluded(5), Included(8)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// let low = Interval::point(10);
    /// let high = Interval::point(25);
    /// assert_eq!(interval_tree.size_between(&low, &high), 5);
    /// ```
    #[must_use]
    pub fn size_between(&self, low_bound: &Interval<T>, high_bound: &Interval<T>) -> usize {
        if self.is_empty() {
            return 0;
        }
        if *low_bound > *high_bound {
            return 0;
        }

        self.rank(high_bound) - self.rank(low_bound) + 1
    }
}

impl<'a, T, V> Debug for IntervalTreeMap<T, V>
where
    T: Debug + Ord + rkyv::Archive + rkyv::Serialize<rkyv::ser::serializers::CompositeSerializer<rkyv::ser::serializers::AlignedSerializer<AlignedVec>, AllocScratch>>,
    V: Debug 
        + rkyv::Archive 
        + rkyv::Serialize<rkyv::ser::serializers::CompositeSerializer<rkyv::ser::serializers::AlignedSerializer<AlignedVec>, AllocScratch>>
{
    fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
        fmt.write_str("IntervalTreeMap ")?;
        fmt.debug_struct("IntervalTreeMap")
            .field("intervals", &self.intervals())
            .field("identifier_map", &self.identifier_map)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::range::Bound::{Excluded, Included, Unbounded};

    #[test]
    fn tree_interval_init() {
        
        let interval_tree = IntervalTreeMap::<usize, ()>::new();
        assert!(interval_tree.is_empty());
        assert_eq!(interval_tree.size(), 0);
    }

    #[test]
    fn tree_interval_insert() {
        let mut interval_tree = IntervalTreeMap::<usize, ()>::new();

        interval_tree.insert(
            Interval::new(Included(0), Included(3)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(5), Included(8)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(6), Included(10)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(8), Included(9)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(15), Included(23)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(16), Included(21)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(17), Included(19)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(19), Included(20)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(25), Included(30)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(26), Included(26)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );

        assert_eq!(interval_tree.size(), 10);
    }

    #[test]
    fn tree_interval_find_overlap_1() {
        let mut interval_tree = IntervalTreeMap::<usize, ()>::new();

        interval_tree.insert(
            Interval::new(Included(0), Included(3)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(5), Included(8)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(6), Included(10)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(8), Included(9)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(15), Included(23)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(16), Included(21)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(17), Included(19)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(19), Included(20)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(25), Included(30)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(26), Included(26)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(1), Included(2)))
                    .unwrap()
            ) == *"[0,3]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(4), Included(5)))
                    .unwrap()
            ) == *"[5,8]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(10), Included(14)))
                    .unwrap()
            ) == *"[6,10]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(14), Included(15)))
                    .unwrap()
            ) == *"[15,23]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(15), Included(18)))
                    .unwrap()
            ) == *"[16,21]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(19), Included(19)))
                    .unwrap()
            ) == *"[19,20]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(23), Included(23)))
                    .unwrap()
            ) == *"[15,23]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(24), Included(26)))
                    .unwrap()
            ) == *"[25,30]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(26), Included(36)))
                    .unwrap()
            ) == *"[25,30]"
        );

        assert!(interval_tree
            .find_overlap(&Interval::new(Included(31), Included(36)))
            .is_none());
        assert!(interval_tree
            .find_overlap(&Interval::new(Included(12), Included(12)))
            .is_none());
        assert!(interval_tree
            .find_overlap(&Interval::new(Included(13), Included(13)))
            .is_none());
        assert!(interval_tree
            .find_overlap(&Interval::new(Included(12), Included(14)))
            .is_none());
    }

    #[test]
    fn tree_interval_find_overlap_2() {
        let mut interval_tree = IntervalTreeMap::<usize, ()>::new();

        interval_tree.insert(
            Interval::new(Included(0), Excluded(3)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(5), Included(8)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(6), Included(10)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(8), Included(9)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(15), Excluded(23)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(16), Excluded(21)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(17), Excluded(19)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(19), Included(20)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(25), Included(30)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(26), Included(26)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(1), Included(2)))
                    .unwrap()
            ) == *"[0,3)"
        );

        assert!(interval_tree
            .find_overlap(&Interval::new(Included(4), Included(5)))
            .is_none());

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(10), Included(14)))
                    .unwrap()
            ) == *"[6,10]"
        );

        assert!(interval_tree
            .find_overlap(&Interval::new(Included(14), Included(15)))
            .is_none());

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(15), Included(18)))
                    .unwrap()
            ) == *"[16,21)"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(19), Included(19)))
                    .unwrap()
            ) == *"[16,21)"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Excluded(23), Included(26)))
                    .unwrap()
            ) == *"(25,30]"
        );

        assert!(interval_tree
            .find_overlap(&Interval::new(Excluded(10), Excluded(15)))
            .is_none());

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Excluded(21), Included(23)))
                    .unwrap()
            ) == *"(15,23)"
        );

        assert!(interval_tree
            .find_overlap(&Interval::new(Included(31), Included(36)))
            .is_none());
        assert!(interval_tree
            .find_overlap(&Interval::new(Included(12), Included(12)))
            .is_none());
        assert!(interval_tree
            .find_overlap(&Interval::new(Included(13), Included(13)))
            .is_none());
        assert!(interval_tree
            .find_overlap(&Interval::new(Included(12), Included(14)))
            .is_none());
    }

    #[test]
    fn tree_interval_find_overlap_3() {
        let mut interval_tree = IntervalTreeMap::<usize, ()>::new();

        interval_tree.insert(
            Interval::new(Unbounded, Excluded(3)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(5), Included(8)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(6), Included(10)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Unbounded, Included(9)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(15), Excluded(23)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Unbounded, Excluded(21)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(17), Excluded(19)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(19), Unbounded), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Unbounded, Included(30)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(26), Unbounded), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(1), Included(2)))
                    .unwrap()
            ) == *"(_,9]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(4), Included(5)))
                    .unwrap()
            ) == *"(_,9]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(10), Included(14)))
                    .unwrap()
            ) == *"(_,21)"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(14), Included(15)))
                    .unwrap()
            ) == *"(_,21)"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(15), Included(18)))
                    .unwrap()
            ) == *"(_,21)"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(19), Included(19)))
                    .unwrap()
            ) == *"(_,21)"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Excluded(23), Included(26)))
                    .unwrap()
            ) == *"(_,30]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Excluded(21), Included(23)))
                    .unwrap()
            ) == *"(_,30]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Unbounded, Included(0)))
                    .unwrap()
            ) == *"(_,9]"
        );
    }

    #[test]
    fn tree_interval_delete_1() {
        let mut interval_tree = IntervalTreeMap::<usize, ()>::new();

        interval_tree.insert(
            Interval::new(Included(0), Included(3)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(5), Included(8)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(6), Included(10)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(8), Included(9)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(15), Included(23)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(16), Included(21)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(17), Included(19)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(19), Included(20)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(25), Included(30)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(26), Included(26)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );

        let mut interval = Interval::new(Included(1), Included(2));
        let mut overlapped_interval = interval_tree.find_overlap(&interval).unwrap();
        interval_tree.delete(&overlapped_interval);
        assert!(interval_tree.find_overlap(&interval).is_none());

        interval = Interval::new(Included(15), Included(18));
        overlapped_interval = interval_tree.find_overlap(&interval).unwrap();
        interval_tree.delete(&overlapped_interval);
        overlapped_interval = interval_tree.find_overlap(&interval).unwrap();
        interval_tree.delete(&overlapped_interval);
        overlapped_interval = interval_tree.find_overlap(&interval).unwrap();
        interval_tree.delete(&overlapped_interval);
        assert!(interval_tree.find_overlap(&interval).is_none());
    }

    #[test]
    fn tree_interval_delete_max_1() {
        let mut interval_tree = IntervalTreeMap::<usize, ()>::new();

        interval_tree.insert(
            Interval::new(Excluded(0), Included(1)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(0), Excluded(3)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(6), Included(10)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(8), Included(9)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(15), Excluded(23)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(16), Excluded(21)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(17), Excluded(19)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(19), Included(20)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(25), Included(30)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(26), Included(26)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );

        interval_tree.delete_max();
        interval_tree.delete_max();

        assert!(interval_tree
            .find_overlap(&Interval::new(Included(23), Included(23)))
            .is_none());
    }

    #[test]
    fn tree_interval_delete_min_1() {
        let mut interval_tree = IntervalTreeMap::<usize, ()>::new();

        interval_tree.insert(
            Interval::new(Included(0), Included(3)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(5), Included(8)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(6), Included(10)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(8), Included(9)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(15), Included(23)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(16), Included(21)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(17), Included(19)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(19), Included(20)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(25), Included(30)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(26), Included(26)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );

        interval_tree.delete_min();
        interval_tree.delete_min();

        assert!(interval_tree
            .find_overlap(&Interval::new(Included(1), Excluded(6)))
            .is_none());
    }

    #[test]
    fn tree_interval_select_1() {
        let mut interval_tree = IntervalTreeMap::<usize, ()>::new();

        interval_tree.insert(
            Interval::new(Excluded(0), Included(1)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(0), Excluded(3)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(6), Included(10)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(8), Included(9)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(15), Excluded(23)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(16), Excluded(21)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(17), Excluded(19)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(19), Included(20)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(25), Included(30)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(26), Included(26)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );

        assert!(format!("{}", interval_tree.select(0).unwrap()) == *"[0,3)");
        assert!(format!("{}", interval_tree.select(1).unwrap()) == *"(0,1]");
        assert!(format!("{}", interval_tree.select(2).unwrap()) == *"[6,10]");
        assert!(format!("{}", interval_tree.select(3).unwrap()) == *"(8,9]");
        assert!(format!("{}", interval_tree.select(4).unwrap()) == *"(15,23)");
        assert!(format!("{}", interval_tree.select(5).unwrap()) == *"[16,21)");
        assert!(format!("{}", interval_tree.select(6).unwrap()) == *"[17,19)");
        assert!(format!("{}", interval_tree.select(7).unwrap()) == *"(19,20]");
        assert!(format!("{}", interval_tree.select(8).unwrap()) == *"(25,30]");
        assert!(format!("{}", interval_tree.select(9).unwrap()) == *"[26,26]");
    }

    #[test]
    fn tree_interval_intervals_between_1() {
        let mut interval_tree = IntervalTreeMap::<usize, ()>::new();

        interval_tree.insert(
            Interval::new(Excluded(0), Included(1)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(0), Excluded(3)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(6), Included(10)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(8), Included(9)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(15), Excluded(23)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(16), Excluded(21)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(17), Excluded(19)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(19), Included(20)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(25), Included(30)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(26), Included(26)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );

        let low = Interval::new(Included(14), Included(14));
        let high = Interval::new(Included(24), Included(24));
        let intervals = interval_tree.intervals_between(&low, &high);

        let accept = String::from("(15,23)[16,21)[17,19)(19,20]");

        let mut result = String::from("");
        for interval in intervals {
            result.push_str(&format!("{}", interval));
        }

        assert_eq!(result, accept);
    }

    #[test]
    fn tree_interval_find_overlaps_1() {
        let mut interval_tree = IntervalTreeMap::<usize, ()>::new();

        interval_tree.insert(
            Interval::new(Excluded(0), Included(1)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(0), Excluded(3)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(6), Included(10)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(8), Included(9)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(15), Excluded(23)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(16), Excluded(21)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(17), Excluded(19)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(19), Included(20)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Excluded(25), Included(30)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        interval_tree.insert(
            Interval::new(Included(26), Included(26)), 
            (), 
            IntervalValueKey::default(), 
            IntervalValueKey::default()
        );
        let interval = Interval::new(Included(8), Included(26));
        let intervals = interval_tree.find_overlaps(&interval);

        let accept = String::from("(8,9][6,10](19,20][16,21)(15,23)[17,19)(25,30][26,26]");

        let mut result = String::from("");
        for interval in intervals {
            result.push_str(&format!("{}", interval));
        }

        assert_eq!(result, accept);
    }

    #[test]
    fn tree_interval_find_overlaps_with_identifier() {
        let mut interval_tree = IntervalTreeMap::<usize, ()>::new();

        // Insert multiple intervals with same identifiers
        interval_tree.insert(
            Interval::new(Excluded(0), Included(1)), 
            (), 
            IntervalValueKey::from("id1"), 
            IntervalValueKey::default());
        interval_tree.insert(Interval::new(Excluded(0), Included(1)), (), IntervalValueKey::from("id1"), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Included(0), Excluded(3)), (), IntervalValueKey::from("id1"), IntervalValueKey::default()); // Same id1
        interval_tree.insert(Interval::new(Included(6), Included(10)), (), IntervalValueKey::from("id2"), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Excluded(8), Included(9)), (), IntervalValueKey::from("id2"), IntervalValueKey::default()); // Same id2
        interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), (), IntervalValueKey::from("id3"), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Included(16), Excluded(21)), (), IntervalValueKey::from("id3"), IntervalValueKey::default()); // Same id3
        interval_tree.insert(Interval::new(Included(17), Excluded(19)), (), IntervalValueKey::from("id4"), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Excluded(19), Included(20)), (), IntervalValueKey::from("id4"), IntervalValueKey::default()); // Same id4
        interval_tree.insert(Interval::new(Excluded(25), Included(30)), (), IntervalValueKey::from("id5"), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Included(26), Included(26)), (), IntervalValueKey::from("id5"), IntervalValueKey::default()); // Same id5

        // Test finding specific intervals by identifier
        let test_interval = Interval::new(Included(16), Included(18));
        
        // Should find id3 interval [16,21) which overlaps with test interval
        let overlap = interval_tree.find_overlap_with_identifier(&test_interval, &IntervalValueKey::from("id3"));
        assert!(overlap.is_some());
        assert_eq!(format!("{}", overlap.unwrap().0), "[16,21)");

        // Should find first overlapping interval with id3
        let test_interval_2 = Interval::new(Included(15), Included(22));
        let overlap_2 = interval_tree.find_overlap_with_identifier(&test_interval_2, &IntervalValueKey::from("id3"));
        assert!(overlap_2.is_some());
        assert_eq!(format!("{}", overlap_2.unwrap().0), "[16,21)");

        // Should find id4 interval [17,19) which overlaps with test interval
        let overlap_id4 = interval_tree.find_overlap_with_identifier(&test_interval, &IntervalValueKey::from("id4"));
        assert_eq!(format!("{}", overlap_id4.unwrap().0), "[17,19)");

        // Test overlaps with intervals sharing same identifier
        let test_interval_3 = Interval::new(Included(0), Included(2));
        let overlap_3 = interval_tree.find_overlap_with_identifier(&test_interval_3, &IntervalValueKey::from("id1"));
        assert!(overlap_3.is_some());
        assert_eq!(format!("{}", overlap_3.unwrap().0), "(0,1]");

        // Should not find non-existent identifier even though interval would overlap
        let wrong_id = interval_tree.find_overlap_with_identifier(&test_interval, &IntervalValueKey::from("wrong_id"));
        assert!(wrong_id.is_none());
    }

    #[test]
    fn tree_interval_query_1() {
        let mut interval_tree = IntervalTreeMap::<usize, ()>::new();

        interval_tree.insert(Interval::new(Excluded(0), Included(1)), (), IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Included(0), Excluded(3)), (), IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Included(6), Included(10)), (), IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Excluded(8), Included(9)), (), IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), (), IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Included(16), Excluded(21)), (), IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Included(17), Excluded(19)), (), IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Excluded(19), Included(20)), (), IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Excluded(25), Included(30)), (), IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Included(26), Included(26)), (), IntervalValueKey::default(), IntervalValueKey::default());

        let interval = Interval::new(Included(8), Included(26));
        let iter = interval_tree.query(&interval);

        let accept = String::from("(8,9][6,10](19,20][16,21)(15,23)[17,19)(25,30][26,26]");

        let mut result = String::from("");
        for entry in iter {
            result.push_str(&format!("{}", entry.interval()));
        }

        assert_eq!(result, accept);
    }

    #[test]
    fn tree_interval_query_2() {
        #[derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize, Default, Debug)]
        #[archive(check_bytes)]
        #[archive_attr(derive(Debug))]
        struct Test {
            bar: bool,
            tool: String
        }

        let mut interval_tree = IntervalTreeMap::<usize, Test>::new();
        interval_tree.insert(Interval::new(Excluded(0), Included(1)), Test { bar: true, tool: "42".to_string() }, IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Included(0), Excluded(3)), Test { bar: false, tool: "17".to_string() }, IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Included(6), Included(7)), Test { bar: true, tool: "99".to_string() }, IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Included(8), Included(9)), Test { bar: false, tool: "123".to_string() }, IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), Test { bar: true, tool: "456".to_string() }, IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Included(16), Excluded(21)), Test { bar: false, tool: "789".to_string() }, IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Included(17), Excluded(19)), Test { bar: true, tool: "321".to_string() }, IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Excluded(19), Included(20)), Test { bar: false, tool: "654".to_string() }, IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Excluded(25), Included(30)), Test { bar: true, tool: "987".to_string() }, IntervalValueKey::default(), IntervalValueKey::default());
        interval_tree.insert(Interval::new(Included(26), Included(26)), Test { bar: false, tool: "246".to_string() }, IntervalValueKey::default(), IntervalValueKey::default());

        let interval = Interval::new(Included(8), Included(9));
        let iter = interval_tree.query_mut(&interval);

        // Serialize to bytes
        let bytes = rkyv::to_bytes::<_, 1024>(&interval_tree).unwrap();
        // Deserialize 
        let deserialized: IntervalTreeMap<usize, Test> = unsafe { rkyv::from_bytes_unchecked::<IntervalTreeMap<usize, Test>>(&bytes).unwrap() };

        // Verify deserialized data
        let iter = deserialized.query(&interval);
        for entry in iter {
            assert!(entry.value().tool == "123".to_string());
        }
    }

    #[test]
    fn tree_interval_debug() {
        let mut interval_tree = IntervalTreeMap::<usize, ()>::new();
        assert_eq!(format!("{:?}", &interval_tree), "IntervalTreeMap {}");
        interval_tree.insert(Interval::new(Excluded(0), Included(1)), (), IntervalValueKey::default(), IntervalValueKey::default());
        assert_eq!(
            format!("{:?}", &interval_tree),
            "IntervalTreeMap {Interval { low: Excluded(0), high: Included(1) }}"
        );
    }
}
