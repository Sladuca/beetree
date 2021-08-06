use std::default::Default;
use std::ptr::NonNull;
use std::cmp::{Ord, Ordering};

#[derive(Debug, Clone, PartialEq)]
pub enum BTree<K: Ord + Clone, V, const Q: usize> {
	// INVARIANT: NonNull always valid
    Internal(NonNull<InternalNode<K, V, Q>>),
	// INVARIANT: NonNull always valid
	Leaf(NonNull<LeafNode<K, V, Q>>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct InternalNode<K: Ord + Clone, V, const Q: usize> {
	keys: Vec<K>,
	// INVARIANT: children.len() == keys.len() + 1
	children: Vec<BTree<K, V, Q>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LeafNode<K: Ord + Clone, V, const Q: usize>
{
	keys: Vec<K>,
	values: Vec<V>,
	// INVARIANS: is Some => NonNull points to valid leaf node
	next: Option<NonNull<LeafNode<K, V, Q>>>,
	// INVARIANT: is Some => NonNull points to valid leaf node
	prev: Option<NonNull<LeafNode<K, V, Q>>>,
}

impl<K, V, const Q: usize> Default for BTree<K, V, Q> 
where
	K: Ord + Clone,
{
	fn default() -> Self {
		assert!(Q > 2, "branching factor Q must be greater than 2");
		let node = unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(LeafNode::default()))) };
		BTree::Leaf(node)
	}
}

impl<K, V, const Q: usize> Default for LeafNode<K, V, Q>
where
	K: Ord + Clone,
{
	fn default() -> Self {
		assert!(Q > 2, "branching factor Q must be greater than 2");
		LeafNode {
			keys: Vec::with_capacity(Q),
			values: Vec::with_capacity(Q),
			next: None,
			prev: None,
		}
	}
}

impl<K, V, const Q: usize> InternalNode<K, V, Q>
where
	K: Ord + Clone,
{

	fn new(child: BTree<K, V, Q>) -> Self {
		assert!(Q > 2, "branching factor Q must be greater than 2");
	
		let mut children = Vec::with_capacity(Q);
		children.push(child);
		
		InternalNode {
			keys: Vec::with_capacity(Q),
			children
		}
	}

	fn insert(&mut self, key: K, child: BTree<K, V, Q>) {
		let idx = self.keys.binary_search(&key).unwrap_or_else(|idx| idx);
		self.keys.insert(idx, key);
		self.children.insert(idx, child);
	}
}

impl<K, V, const Q: usize> LeafNode<K, V, Q>
where
	K: Ord + Clone,
{
	fn insert(&mut self, key: K, value: V) {
		let idx = self.keys.binary_search(&key).unwrap_or_else(|idx| idx);
		self.keys.insert(idx, key);
		self.values.insert(idx, value);
	}
}

impl<K, V, const Q: usize> BTree<K, V, Q>
where
	K: Ord + Clone,
{

	fn insert_inner(&mut self, key: K, value: V) -> Option<(K, BTree<K, V, Q>)> {
		match self {
			BTree::Leaf(ref mut _leaf) => {
				// SAFETY: OK due to invariant
				let leaf = unsafe { _leaf.as_mut() };
				leaf.insert(key, value);
				if leaf.keys.len() == Q {
					let mid = leaf.keys.len() / 2;

					let mut right: LeafNode<K, V, Q> = Default::default();
					right.keys = leaf.keys.split_off(mid);
					right.values = leaf.values.split_off(mid);

					let right = Box::new(right);
					let split_key = right.keys[0].clone();

					// SAFETY: right is valid pointer
					let mut right = unsafe { NonNull::new_unchecked(Box::into_raw(right)) };	
					// SAFETY: _leaf is valid pointer due to invariant
					unsafe { right.as_mut().prev = Some(*_leaf) };
					leaf.next = Some(right);

					Some((split_key, BTree::Leaf(right)))
				} else {
					None
				}
			}
			BTree::Internal(ref mut node) => {
				// SAFETY: OK due to invariant
				let node = unsafe { node.as_mut() };

				let idx = node.keys.binary_search(&key).unwrap_or_else(|idx| idx);
				if let Some((split_key, child)) = node.children[idx].insert_inner(key, value) {

					node.insert(split_key, child);

					if node.keys.len() == Q {
						let mid = node.keys.len() / 2;

						let right_keys = node.keys.split_off(mid+1);
						let right_children  = node.children.split_off(mid+1);
						
						// unwrap() OK here because Q >= 3 => node.keys.len() >= 3
						// => after split, node.keys.len() > 1
						// => after split, node.children.len() > 1 due to invariant (children.len() == keys.len() + 1)
						let split_key = node.keys.pop().unwrap();
						let split_child = node.children.pop().unwrap();

						let mut right = InternalNode::new(split_child);
						right.keys.extend(right_keys);
						right.children.extend(right_children);

						let right = Box::new(right);
						
						// SAFETY: right is valid pointer
						let right = unsafe { NonNull::new_unchecked(Box::into_raw(right)) };
						Some((split_key, BTree::Internal(right)))
					} else {
						None
					}
				} else {
					None
				}
			}
		}
	}

	pub fn insert(&mut self, key: K, value: V) {
		// if insert_inner returns Some, need to make a new root
		// otherwise, we're done
		if let Some((right_key, right)) = self.insert_inner(key, value) {


			let new_root = InternalNode::new(right);
			let new_root = Box::new(new_root);
			// SAFETY: new_root is valid pointer due to box
			let new_root = unsafe { NonNull::new_unchecked(Box::into_raw(new_root)) };

			let left = std::mem::replace(self, BTree::Internal(new_root));
			match self {
				BTree::Internal(ref mut node) => {
					// SAFETY: node is valid pointer because self is new root, which is valid pointer
					let node = unsafe { node.as_mut() };

					node.keys.push(right_key);
					node.children.insert(0, left);
				},
				BTree::Leaf(_) => panic!("expected root to be Internal node!")
			}
		}
	}

	pub fn search(&self, key: &K) -> Option<&V> {
		match self {
			BTree::Internal(ref node) => {
				// SAFETY: Ok due to invariant
				let idx = unsafe { node.as_ref() }.keys.binary_search(key).unwrap_or_else(|idx| idx);
				unsafe { node.as_ref() }.children[idx].search(key)
			},
			BTree::Leaf(ref node) => {
				// SAFETY: Ok due to invariant
				let idx = unsafe { node.as_ref() }.keys.binary_search(key).ok();
				match idx {
					// SAFETY: Ok due to invariant
					Some(idx) => Some(&(unsafe { node.as_ref() }.values[idx])),
					None => None
				}
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::fmt::Debug;

	fn is_sorted<T: Ord>(items: &Vec<T>) -> bool {
		let (is_sorted, _) = items.iter().fold((true, None), |(is_sorted, prev), curr| {
			if let Some(prev) = prev {
				(is_sorted && prev <= curr, Some(curr))
			} else {
				(is_sorted, Some(curr))
			}
		});

		is_sorted
	}

	fn assert_at_node<K: Debug>(cond: bool, left_parent_key: Option<&K>, level: usize, msg: String) {
		assert!(
			cond,
			format!("In node with parent key {:#?} at level {}: {}", left_parent_key, level, msg)
		);
	}
	
	fn assert_is_b_tree_inner<K: Ord + Clone + Debug, V, const Q: usize>(node: &BTree<K, V, Q>, parent_keys: (Option<&K>, Option<&K>), level: usize) {
		let (left_parent_key, right_parent_key) = parent_keys;

		match node {
			BTree::Internal(ptr) => {
				// SAFETY: ptr validity guaratnteed by invariant
				let node = unsafe { ptr.as_ref() };

				assert_at_node(
					is_sorted(&node.keys),
					left_parent_key,
					level,
					"keys are not sorted".to_string()
				);

				// ensure every key in node is >= left parent key but < right parent key
				// ignore the corresponding check of each parent key that is None
				node.keys.iter().for_each(|key| match (left_parent_key, right_parent_key) {
					(Some(left), Some(right)) => {
						assert_at_node(
							key >= left && key < right,
							left_parent_key,
							level,
							format!("key {:#?} < left parent key {:#?} or >= right parent key {:#?}", key, left, right)
						)
					},
					(Some(left), None) => {
						assert_at_node(
							key >= left,
							left_parent_key,
							level,
							format!("key {:#?} < left parent key {:#?}", key, left)

						)
					},
					(None, Some(right)) => {
						assert_at_node(
							key < right,
							left_parent_key,
							level,
							format!("key {:#?} >= right parent key {:#?}", key, right)
						)
					},
					(None, None) => {
						assert_at_node(
							level == 0,
							left_parent_key,
							level,
							"(None, None) case of parent keys for non-root node encountered!".to_string()
						)
					}
				});

				node.children.iter().enumerate().for_each(|(i, child)| {
					// recurse - parent keys have 4 possible cases
					if i == 0 && i == node.keys.len() - 1 {
						// case where there's only 1 child - should never happen
						assert_at_node(
							false,
							left_parent_key,
							level,
							"only 1 child!".to_string()
						);
					} else if i == 0 {
						// case where it's the 0th but not the last child
						let right = &node.keys[i];
						assert_is_b_tree_inner(child, (None, Some(right)), level + 1);
					} else if i == node.keys.len() {
						// case where it's the last child
						let left = &node.keys[i-1];
						assert_is_b_tree_inner(child, (Some(left), None), level + 1);
					} else {
						// case where it's neither the first nor the last child
						let left = &node.keys[i-1];
						let right = &node.keys[i];
						assert_is_b_tree_inner(child, (Some(left), Some(right)), level + 1);
					}
				});
			},
			BTree::Leaf(ptr) => {
				// SAFETY: ptr validity guaranteed by invariant
				let node = unsafe { ptr.as_ref() };

				assert_at_node(
					node.keys.len() >= Q / 2,
					left_parent_key,
					level,
					format!("leaf node has {} < Q / 2 keys", node.keys.len())
				);

				assert_at_node(
					is_sorted(&node.keys),
					left_parent_key,
					level,
					"keys are not sorted".to_string()
				);

				// check key of leaf node to the left, if it exists
				let (left_leaf_last_key, is_lte) = node.prev.map_or((None, true), |ptr| {
					// SAFETY: guaranteed by invariant that Some => ptr is valid
					let left_leaf = unsafe { ptr.as_ref() };
					
					// if left_leaf.keys.last() is None the keys.len() assertion will catch this bug
					// ignore that case
					if let Some(left_leaf_last_key) = left_leaf.keys.last() {
						(Some(left_leaf_last_key), left_leaf_last_key <= node.keys.first().unwrap())
					} else {
						(None, true)
					}
				});
				
				assert_at_node(
					is_lte,
					
					left_parent_key,
					level,
					format!(
						"last key {:#?} of left leaf node > {:#?}, first key of current leaf node",
						node.keys.first().unwrap(),
						left_leaf_last_key
					)
				);

				// check key of node to the right, if it exists
				let (right_leaf_first_key, is_gte) = node.next.map_or((None, true), |ptr| {
					// SAFETY: guaranteed by invariant that Some => ptr is valid
					let right_leaf = unsafe { ptr.as_ref() };
					
					// if left_leaf.keys.last() is None the keys.len() assertion will catch this bug
					// ignore that case
					if let Some(right_leaf_first_key) = right_leaf.keys.first() {
						(Some(right_leaf_first_key), right_leaf_first_key <= node.keys.last().unwrap())
					} else {
						(None, true)
					}
				});
				
				assert_at_node(
					is_gte,
					
					left_parent_key,
					level,
					format!(
						"first key {:#?} of right leaf node < {:#?}, last key of current leaf node",
						node.keys.last().unwrap(),
						right_leaf_first_key
					)
				)
			}
		}
	}

	fn assert_is_b_tree<K: Ord + Clone + Debug, V, const Q: usize>(root: &BTree<K, V, Q>) {
		assert_is_b_tree_inner(root, (None, None), 0)
	}
}
