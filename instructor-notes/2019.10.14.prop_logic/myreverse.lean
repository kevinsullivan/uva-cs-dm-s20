def app {α : Type} : list α → list α → list α 
| list.nil l := l
| (list.cons h t) l := list.cons h (app t l)

def rev {α : Type} : list α → list α
| list.nil := list.nil
| (list.cons h t) := app (rev t) (list.cons h list.nil)
--list.cons (rev t) h

#reduce rev [1,2,3,4,5,6]

