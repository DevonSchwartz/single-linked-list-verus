use vstd::prelude::*;

mod list;

verus! {
use list::*;

fn main() {
    let mut list1 = LList::new(); 

    list1.push(3);
    list1.push(4);
    list1.push(5);

}

// fn deepCopy(list1 : &LList) -> list2 : LList 
//     ensures
//         list1@ =~= list2@
// {
//     let list2 = LList::new(); 
//     let it1 = list1.iterato
// }
}
