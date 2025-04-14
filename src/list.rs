use vstd::prelude::*;
verus! {

// List<T> is a singly linked list
struct LList<T> {
    head: Option<Box<Node<T>>>,
    len: usize,
}

pub struct Node<T> {
    pub data: T,
    pub next: Option<Box<Node<T>>>,
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

    fn remove_next(&mut self) -> (old_val: T)
        requires
            old(self).next.is_some(),
        ensures
            self@ =~= old(self)@.drop_last(),
            old(self)@.last() == old_val,
            self@.len() == old(self)@.len() - 1,
    {
        let mut remove_node = *self.next.take().unwrap();

        if (remove_node.next.is_none()) {
            // assert(remove_node@.len() == 1);
            self.next = None;
            assert(self.next.is_none());
            assert(self@.len() == 1);
            // assert(self@.skip(1) =~= seq![]);
            assert(remove_node@[0] == remove_node.data);
            assert(self@ == old(self)@.drop_last());
            return remove_node.data;
        }
        assert(remove_node.next.is_some());

        let removed_val = remove_node.remove_next();
        self.next = Some(Box::new(remove_node));

        assert(self.next.is_some());
        assert(self.next.unwrap()@ =~= self@.skip(1));

        assert(self@ =~= old(self)@.drop_last());
        assert(self@.len() == old(self)@.len() - 1);
        removed_val
    }

    fn remove_middle(&mut self, index: usize) -> (old_val: T)
        requires
            1 <= index < old(self)@.len(),
            old(self).next.is_some(),
        ensures
            self@ =~= old(self)@.remove(index as int),
            old(self)@[index as int] == old_val,
            self@.len() == old(self)@.len() - 1,
    {
        let mut remove_node = *self.next.take().unwrap();

        if (index == 1) {
            self.next = remove_node.next;
            assert(self.next == remove_node.next);
            assert(self.next.unwrap()@ =~= remove_node.next.unwrap()@);

            assert(self@ =~= old(self)@.remove(index as int));
            assert(self@ =~= seq![old(self)@[0]] + old(self)@.skip(2));


            return remove_node.data;
        }
        let removed_val = remove_node.remove_middle(index - 1);
        self.next = Some(Box::new(remove_node));
        removed_val
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
                curr_index <= index < self@.len(),  // why is this invariant necessary if covered by loop condition? **Maybe
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
            old(self)@.len() > 0,
        ensures
            self@.len() == old(self)@.len() - 1,
            self@ =~= old(self)@.remove(0),
            old(self)@[0] == old_val,
    {
        let old_head = self.head.take().unwrap();
        self.head = old_head.next;
        self.len = self.len - 1;
        // TODO: remove assume and prove
        assume(old(self)@[0] == old_head.data);
        old_head.data
    }

    fn remove_last(&mut self) -> (old_val: T)
        requires
            old(self).len > 0,
            old(self)@.len() > 0,
        ensures
            self@.len() == old(self)@.len() - 1,
            self@ =~= old(self)@.drop_last(),
            old(self)@.last() == old_val,
    {
        let mut head = *self.head.take().unwrap();

        let removed_data = match head.next {
            Some(_) => {
                let data = head.remove_next();
                self.head = Some(Box::new(head));
                data
            },
            None => {
                let data = head.data;
                self.head = None;
                data
            },
        };

        self.len = self.len - 1;
        removed_data
    }

    fn remove(&mut self, index: usize) -> (old_val: T)
        requires
            index < old(self)@.len(),
            old(self).len > 0,
            old(self)@.len() > 0,
        ensures
            self@.len() == old(self)@.len() - 1,
            self@ =~= old(self)@.remove(index as int),
            old(self)@[index as int] == old_val,
    {
        if (index == 0) {
            return self.remove_front();
        }
        assert(self@.len() >= 2); 
        assert(index >= 1); 

        let mut head = *self.head.take().unwrap();
        let removed_data = head.remove_middle(index);
        self.head = Some(Box::new(head)); 
        self.len = self.len - 1;
        removed_data
    }
}

pub struct LLIter<'a, T> {
    pub list: &'a LList<T>,
    pub curr_node: Option<&'a Box<Node<T>>>
}

impl<'a,T> LLIter<'a, T> {
    fn new(list: &'a mut LList<T>) -> LLIter<'a, T>
        // requires
        //     old(list).head is Some,
    {
        LLIter {
            list,
            // curr_node: list.head.as_ref().unwrap(),
            curr_node: list.head.as_ref(),
        }
    }
}

impl<'a,T> Iterator for LLIter<'a, T> {

    type Item = &'a T; 


    // TODO:
    // - is this function supposed to return the old or the new value?
    // - if it returns the old value, may need to change how we handle the end of the tail
    // - need fix up the postcondition in the Some case
    // - need to specify what happens to curr_node
    fn next(&mut self) -> (result: Option<Self::Item>)
        ensures 
            old(self).curr_node is None ==> result is None,
            old(self).curr_node is Some ==> result == Some(&old(self).curr_node.unwrap().data)
    {
        // options: 1. return none don't change curr_node at end
        // 2. store an option around node and set to none at end of list

        let returnedData = match self.curr_node {
            Some(node) => Some(&node.data),
            None => None
        };


        if (self.curr_node.is_some()) {
            // let old_data = &self.curr_node.unwrap().data;
            // assert(old_data == self.curr_node.unwrap().data); 
            // assert(returnedData == Some(self.curr_node.unwrap().data)); 
            // let old_node = self.curr_node.unwrap();
            // assert(Some(old_node) == self.curr_node); 
            // assert(Some(old_node.data) == Some(self.curr_node.unwrap().data)); 

            // self.curr_node = self.curr_node.next.as_ref().unwrap();
            self.curr_node = self.curr_node.unwrap().next.as_ref();


            // // assert(self.curr_node@ =~= old_node@.skip(1));
            // // assert(old_node == )

            // let cloned_data = old_node.data.clone();
            // assume(Some(cloned_data) == Some(old_node.data)); // TODO: fix -- look into specification for clone
            // return Some(old_node.data.clone()); 
        }
        // assert(self.curr_node is None);
        return returnedData; 
    }
}
}