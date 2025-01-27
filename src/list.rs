use vstd::prelude::*;
verus! {

    use vstd::simple_pptr::*;
    use vstd::raw_ptr::MemContents;

    // List<T> is a singly linked list
    struct LList<T>{
        head: Option<Box<Node<T>>>,
        len: usize,
    }

    struct Node<T>{
        data: T,
        next: Option<Box<Node<T>>>,
    }


    impl<T> Node<T> {

        // this terminates on a null-terminated node
        spec fn optional_as_seq(node_opt: Option<Box<Node<T>>>) -> Seq<T>
            decreases node_opt, // demonstrate that recursion will terminate
        {
            match node_opt {
                None => Seq::empty(),
                Some(node) => node.as_seq(),
            }
        }

        // **Taken from Verus Tutorial on Treemap. Unsure how this works to interpret the linked list as a Seq**
        spec fn as_seq(self) -> Seq<T>
            decreases self,
        {
            // Node<T>::optional_as_seq(self.next).insert(self.data)
            seq![self.data] + Node<T>::optional_as_seq(self.next)
        }
    }

    impl<T> LList<T> {

        // do not show body outside module. This means that calls to this outside module
        // will not know as)seq calls optional_as_seq, which returns Seq<T>
        pub closed spec fn as_seq(self) -> Seq<T> {
            Node::<V>::optional_as_seq(self.head)
        }
    }

    impl<T> View for LList<T> {
        type V = Seq<T>;

        // the view of the LList should be a sequence. This needs to be open so it is usable by
        // outside module
        open spec fn view(&self) -> Seq<T> {
            self.as_seq() // IS THIS TREATED LIKE "closed" HERE?
        }
    }

    impl <T> LList<T> {
        // Node at index i is well formed
        spec fn well_formed_node(&self, i: int) -> bool
        {
            &&& (i < self@.len)
            &&& (i >= 0)
            // what other properties would be here?
        }
    }

} // verus!
