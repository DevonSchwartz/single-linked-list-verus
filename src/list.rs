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

    fn set_next(&mut self, append: Node<T>)
        requires
            append.next.is_none(),
        ensures
            self@ == old(self)@.push(append.data),
    {
        if (self.next.is_none()) {
            assert(self@.len() == 1);
            assert(self@[0] == self.data);
            self.next = Some(Box::new(append));

            // show that the pushed nodes sequence is the same as the current nodes sequence with the current node truncated
            assert(self.next.unwrap()@ =~= self@.skip(1));

            assert(self@[1] == append.data);
            assert(self@.len() == 2);
            assert(self@ == old(self)@.push(append.data));
        } else {
            //set to variable call recursively
            let mut next = *self.next.take().unwrap();
            next.set_next(append);
            self.next = Some(Box::new(next));
            assert(self@ == old(self)@.push(append.data));
        }
    }
}

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
            out@ == Seq::<T>::empty(),  // empty

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
                curr_index <= index
                    < self@.len(),  // why is this invariant necessary if covered by loop condition? **Maybe

        {
            assert(temp.unwrap().next.unwrap()@ =~= temp.unwrap()@.skip(1));
            temp = &temp.as_ref().unwrap().next;
            curr_index += 1;
        }

        assert(temp.unwrap()@ == seq![temp.unwrap().data] + match temp.unwrap().next {
            Some(n) => n.view(),
            None => seq![],
        });  // assert extensional equality

        assert(temp.unwrap()@[0] == temp.unwrap().data);  // needed to prove postcondition
        return &temp.as_ref().unwrap().data;
    }

    fn push(&mut self, val: T)
        requires
            old(self).len < usize::MAX,
        ensures
            self@.len() == old(self)@.len() + 1,
            self@ == old(self)@.push(val),
    {
        let append = Node { data: val, next: None };

        if (self.head.is_none()) {
            self.head = Some(Box::new(append));
        } else {
            let mut head = *self.head.take().unwrap();
            head.set_next(append);
            self.head = Some(Box::new(head));
        }

        self.len = self.len + 1;
    }

    fn push_front(&mut self, val: T)
        requires
            old(self).len < usize::MAX,
        ensures
            self@.len() == old(self)@.len() + 1,
            self@ =~= seq![val] + old(self)@,
    {
        // code heavily sourced from https://github.com/verus-lang/paper-sosp24-artifact/blob/main/milli/linked-list/verus.rs
        let next = self.head.take();
        self.head = Some(Box::new(Node { data: val, next: next }));
        self.len = self.len + 1;
    }

    fn remove_front(&mut self) -> (old_val: T)
        requires
            old(self).len > 0,
            old(self)@.len() > 0
        ensures
            self@.len() == old(self)@.len() - 1,
            self@ =~= old(self)@.skip(1),
            old(self)@[0] == old_val,
    {
        let old_head = self.head.take().unwrap();
        self.head = old_head.next;
        self.len = self.len - 1; 
        old_head.data
    }
}

} // verus!
