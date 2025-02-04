use std::{sync::Arc, boxed::Box};
use std::collections::BTreeSet;
use core::{
    cmp::{max, Ord},
};
use crate::range::Bound::{self, Excluded, Included, Unbounded};
use crate::IntervalValueKey;
use crate::SerializableRwLock;
use rkyv::*;
use crate::interval::Interval;

#[derive(Debug, PartialEq, Clone, serde::Serialize, serde::Deserialize)]
#[derive(rkyv::Archive, rkyv::Deserialize, rkyv::Serialize)]
#[archive(check_bytes)]
#[archive(bound(serialize = "T: rkyv::Serialize<__S>, V: rkyv::Serialize<__S>, __S: rkyv::ser::Serializer + rkyv::ser::SharedSerializeRegistry"))]
#[archive(bound(deserialize = "T: rkyv::Archive, V: rkyv::Archive, <T as rkyv::Archive>::Archived: rkyv::Deserialize<T, __D>, <V as rkyv::Archive>::Archived: rkyv::Deserialize<V, __D>, __D: rkyv::de::SharedDeserializeRegistry"))]
pub(crate) struct Node<T: Ord + rkyv::Archive, V: rkyv::Archive> {

    pub interval: Option<Interval<T>>,
    pub value: Option<Arc<SerializableRwLock<V>>>,
    pub identifier: Option<IntervalValueKey>,
    pub max: Option<Arc<Bound<T>>>,
    pub height: usize,
    pub size: usize,

    // Set of all identifiers in this subtree (another compared value).
    pub subtree_identifiers: BTreeSet<IntervalValueKey>,
    #[omit_bounds]
    pub left_child: Option<Box<Node<T, V>>>,
    #[omit_bounds]
    pub right_child: Option<Box<Node<T, V>>>,
    // Used to constant time access to the value in the node
    pub value_key: IntervalValueKey,
}

impl<T: Ord + rkyv::Archive, V: rkyv::Archive> Node<T, V> {
    pub fn init(
        interval: Interval<T>,
        value: Arc<SerializableRwLock<V>>,
        max: Arc<Bound<T>>,
        identifier: IntervalValueKey,
        height: usize,
        size: usize,
        value_key: IntervalValueKey,
    ) -> Node<T, V> {
        let mut subtree_identifiers = BTreeSet::new();
        subtree_identifiers.insert(identifier.clone());

        Node {
            interval: Some(interval),
            value: Some(value),
            identifier: Some(identifier),
            max: Some(max),
            height,
            size,
            subtree_identifiers,
            left_child: None,
            right_child: None,
            value_key,
        }
    }

    pub fn value(&self) -> &Arc<SerializableRwLock<V>> {
        self.value.as_ref().unwrap()
    }

    pub fn value_mut(&mut self) -> &mut Arc<SerializableRwLock<V>> {
        self.value.as_mut().unwrap()
    }

    pub fn option_value_mut(&mut self) -> Option<&mut Arc<SerializableRwLock<V>>> {
        self.value.as_mut()
    }

    pub fn option_value_mut_with_interval_and_key(&mut self) -> (Option<&Interval<T>>, Option<&mut Arc<SerializableRwLock<V>>>, Option<&IntervalValueKey>) {
        (self.interval.as_ref(), self.value.as_mut(), Some(&self.value_key))
    }

    /// Updates the set of identifiers in this node's subtree by combining:
    /// 1. This node's identifier
    /// 2. All identifiers from the left subtree
    /// 3. All identifiers from the right subtree
    ///
    /// This maintains the invariant that each node's subtree_identifiers contains
    /// all identifiers in its subtree, which enables efficient overlap queries by
    /// checking if any intervals with matching identifiers overlap the query interval.
    /// The identifiers are stored in a balanced BTreeSet for O(log n) operations.
    pub fn update_identifiers(&mut self) {
        let mut identifiers = BTreeSet::new();
        
        // Add current node's identifier
        if let Some(ref id) = self.identifier {
            identifiers.insert(id.clone());
        }

        // Add identifiers from left child
        if let Some(ref left) = self.left_child {
            identifiers.extend(left.subtree_identifiers.iter().cloned());
        }
        
        // Add identifiers from right child
        if let Some(ref right) = self.right_child {
            identifiers.extend(right.subtree_identifiers.iter().cloned());
        }

        self.subtree_identifiers = identifiers;
    }

    // fn value_mut(&mut self) -> &mut V {
    //    self.value.as_mut().unwrap()
    //}

    pub fn get_value(&mut self) -> Arc<SerializableRwLock<V>> {
        self.value.take().unwrap()
    }

    pub fn value_key(&self) -> &IntervalValueKey {
        &self.value_key
    }

    pub fn interval(&self) -> &Interval<T> {
        self.interval.as_ref().unwrap()
    }

    pub fn get_interval(&mut self) -> Interval<T> {
        self.interval.take().unwrap()
    }

    pub fn get_identifier(&mut self) -> IntervalValueKey {
        self.identifier.take().unwrap()
    }

    pub fn get_max(&self) -> Arc<Bound<T>> {
        Arc::clone(self.max.as_ref().unwrap())
    }

    // _max_height is at least -1, so +1 is a least 0 - and it can never be higher than usize
    #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
    pub fn update_height(&mut self) {
        self.height = (1 + Node::_max_height(&self.left_child, &self.right_child)) as usize;
    }

    pub fn update_size(&mut self) {
        self.size = 1 + Node::size(&self.left_child) + Node::size(&self.right_child);
    }

    pub fn update_max(&mut self) {
        let max = match (&self.left_child, &self.right_child) {
            (Some(left_child), Some(right_child)) => Node::<T, V>::find_max(
                self.interval().get_high(),
                Node::<T, V>::find_max(left_child.get_max(), right_child.get_max()),
            ),
            (Some(left_child), None) => {
                Node::<T, V>::find_max(self.interval().get_high(), left_child.get_max())
            }
            (None, Some(right_child)) => {
                Node::<T, V>::find_max(self.interval().get_high(), right_child.get_max())
            }
            (None, None) => self.interval().get_high(),
        };

        self.max = Some(Arc::clone(&max));
    }

    pub fn find_max(bound1: Arc<Bound<T>>, bound2: Arc<Bound<T>>) -> Arc<Bound<T>> {
        match (bound1.as_ref(), bound2.as_ref()) {
            (Included(val1), Included(val2) | Excluded(val2))
            | (Excluded(val1), Excluded(val2)) => {
                if val1 >= val2 {
                    bound1
                } else {
                    bound2
                }
            }
            (Excluded(val1), Included(val2)) => {
                if val1 > val2 {
                    bound1
                } else {
                    bound2
                }
            }
            (Unbounded, _) => bound1,
            (_, Unbounded) => bound2,
        }
    }

    pub fn is_ge(bound1: &Arc<Bound<T>>, bound2: &Arc<Bound<T>>) -> bool {
        match (bound1.as_ref(), bound2.as_ref()) {
            (Included(val1), Included(val2)) => val1 >= val2,
            (Included(val1) | Excluded(val1), Excluded(val2))
            | (Excluded(val1), Included(val2)) => val1 > val2,

            (Unbounded, Included(_val2)) => true,
            (Unbounded, Excluded(_val2)) => true,
            (Included(_val1), Unbounded) => true,
            (Excluded(_val1), Unbounded) => true,

            (Unbounded, Unbounded) => true,
        }
    }

    pub fn _max_height(node1: &Option<Box<Node<T, V>>>, node2: &Option<Box<Node<T, V>>>) -> i64 {
        max(Node::height(node1), Node::height(node2))
    }

    pub fn height(node: &Option<Box<Node<T, V>>>) -> i64 {
        match node {
            Some(node) => node.height as i64,
            None => -1,
        }
    }

    pub fn size(node: &Option<Box<Node<T, V>>>) -> usize {
        match node {
            Some(node) => node.size,
            None => 0,
        }
    }

    pub fn balance_factor(node: &Node<T, V>) -> i64 {
        Node::height(&node.left_child) - Node::height(&node.right_child)
    }
}
