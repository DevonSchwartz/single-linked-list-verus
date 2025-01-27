use vstd::prelude::*;
verus! {


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
                None       => Seq::empty(),
                Some(node) => node.as_seq(),
            }
        }

        // **Taken from Verus Tutorial on Treemap. Unsure how this works to interpret the linked list as a Seq**
        spec fn as_seq(self) -> Seq<T>
            decreases self,
        {
            // Node<T>::optional_as_seq(self.next).insert(self.data)
            seq![self.data] + Node::<T>::optional_as_seq(self.next)
        }
    }

    impl<T> LList<T> {

        // do not show body outside module. This means that calls to this outside module
        // will not know as)seq calls optional_as_seq, which returns Seq<T>
        pub closed spec fn as_seq(self) -> Seq<T> {
            Node::<T>::optional_as_seq(self.head)
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

    // executable functionality 
    impl<T> LList<T> {
        fn new() -> (out: Self)
            ensures out@.len() == 0, // empty
        {
            Self {
                head: None,
                len: 0 
            } // return empty list 
        }

        fn get(&self, index: usize) -> (out: &T)
            requires index < self@.len()
            ensures self@[index as int] == out
        {
            Node<T> temp = Self.head; 
            let curr_index = 0; 

            let ghost old = self@; 


            while (curr_index < index) 
                invariant
                    self@ == old,
                    self@[curr_index] == temp.data 
            {
                // TODO: Implement while loop 
            }
        }
    }

} // verus!
