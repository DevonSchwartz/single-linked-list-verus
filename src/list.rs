use vstd::prelude::*;
verus! {

// List<T> is a singly linked list
struct LList<T> {
    head: Option<Box<Node<T>>>,
    len: usize,
}

struct Node<T> {
    data: T,
    next: Option<Box<Node<T>>>,
}

impl<T> Node<T> {
    closed spec fn view(&self) -> Seq<T>
        decreases self,
    {
        seq![self.data] + match self.next {
            Some(n) => n.view(),
            None => seq![],
        }
    }
}

// impl<T> LList<T> {
//     // do not show body outside module. This means that calls to this outside module
//     // will not know as)seq calls optional_as_seq, which returns Seq<T>
//     // pub closed spec fn as_seq(self) -> Seq<T> {
//     //     Node::<T>::optional_as_seq(self.head)
//     // }
//     // proof fn lemma_view_values_equals_seq(self, i: int, current_node:Box<Node<T>>)
//     //     requires
//     //         self@.len() == self.len,
//     //         i >= 0,
//     //         i < self.len,
//     //         self@[i] == current_node.data,
//     //         i == self.len - 1 ==> current_node.next is None,
//     //         i < self.len - 1 ==> current_node.next is Some,
//     //     ensures
//     //         i < self.len - 1 ==> self@[i + 1] == current_node.next.unwrap().data,
//     //         i == self.len - 1 ==> current_node.next is None,
//     //     decreases self.len - 1 - i
//     // {
//     //     // if (current_node.next is None) {
//     //     //     assert(i == self.len - 1);
//     //     //     //base case
//     //     // }
//     //     if (i == self.len - 1) {
//     //         // base case
//     //     }
//     //     else {
//     //         assert(current_node.next is Some);
//     //         assert( seq![current_node.data] + current_node.next.unwrap().as_seq() == self@.subrange(i, self@.len() as int));
//     //         assert(current_node.as_seq() == seq![current_node.data] + current_node.next.unwrap().as_seq());
//     //         assert(current_node.as_seq() == self@.subrange(i, self@.len() as int));
//     //         //recursively call until end of list
//     //         self.lemma_view_values_equals_seq(i + 1, current_node.next.unwrap());
//     //     }
//     // }

// }

impl<T> View for LList<T> {
    type V = Seq<T>;

    // the view of the LList should be a sequence. This needs to be open so it is usable by
    // outside module
    closed spec fn view(&self) -> Seq<T>
        decreases self,
    {
        match self.head {
            Some(h) => h.view(),
            None => seq![],
        }
    }
}

// executable functionality
impl<T> LList<T> {
    fn new() -> (out: Self)
        ensures
            out@.len() == 0,
            out@ == Seq::<T>::empty()  // empty
    {
        Self { head: None, len: 0 }  // return empty list

    }

    //TODO: Add proof function to show sequence is equivalent to linked list
    fn get(&self, index: usize) -> (out: &T)
        requires
            index < self@.len(),
        ensures
            self@[index as int] == out,
    {
        let mut temp = &self.head;
        let mut curr_index = 0;

        while (curr_index < index)
            invariant
                temp.is_some() && temp.unwrap()@ =~= self@.skip(curr_index as int),
                curr_index <= index < self@.len() // why is this invariant necessary if covered by loop condition? 

        {
            assert(temp.unwrap().next.unwrap()@ =~= temp.unwrap()@.skip(1));
            temp = &temp.as_ref().unwrap().next;
            curr_index += 1;
        }
        assert(temp.unwrap()@ == seq![temp.unwrap().data] + match temp.unwrap().next {
            Some(n) => n.view(),
            None => seq![],
        });

        assert(temp.unwrap()@[0] == temp.unwrap().data);
        return &temp.as_ref().unwrap().data;
    }
}

} // verus!
