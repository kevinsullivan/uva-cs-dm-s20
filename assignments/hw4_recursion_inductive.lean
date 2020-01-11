/-
Problem #1. We give you a simple "natural 
number arithmetic abstract data type. We
call our datatype for representing natural 
numbers mnat. You are to extend the basic
abstract data type we give you by adding 
definitions of several new operations
(functions). 

The first is a boolean "less than" 
operator. It will take two natural 
numbers (mnat values)and return true 
(tt) if and only if the first is less
than the second (otherwise it will
return false). 

The second function will implement mnat
multiplication. It will use recursion and
the given definition of mnat addition in
this implementation.

The third function will implement the
factorial function using the mnat type.
The factorial of zero is one and the 
factorial of any number n = 1 + n' is
n times the factorial of n'. 
-/

-- Here's the mnat data type.

inductive mnat : Type
| zero
| succ : mnat → mnat

open mnat 

-- Here's an increment function, that
-- takes an mnat returns the next mnat 
def inc : mnat → mnat :=
    λ n : mnat, succ n

-- alternative syntax (c-style)
def inc' (n : mnat) : mnat :=
    succ n

-- is_zero predicate: returns tt if
-- and only if a given mnat is zero 
def is_zero : mnat → bool
| zero := tt
| _ := ff

-- predecessor
-- returns zero when mnat is zero
-- else returns one less than given mnat
def pred : mnat → mnat 
| zero := zero
| (succ m) := m

-- equality predicate, takes two mnats,
-- returns tt if they are equal, else ff
def eq_mnat : mnat → mnat → bool
| zero zero := tt 
| zero (succ m) := ff
| (succ m) zero := ff
| (succ m) (succ n) := eq_mnat m n

-- mnat addition
-- zero + any m returns m
-- (1 + n') + m returns 1 + (m' + n)
def add_mnat : mnat → mnat → mnat
| zero m := m
| (succ n') m := succ (add_mnat n' m)


/- [10 points]
#1A. Implement an mnat "less than" 
predicate by completing the following 
definition. Fill in the placeholders.
-/

def lt_mnat : mnat → mnat → bool
| zero zero := _
| zero _ := _
| (succ n') zero := _
| (succ n') (succ m') := _


-- Here are names for the first few mnats
def mzero := zero
def mone := succ zero
def mtwo := succ (succ zero)
def mthree := succ (succ (succ zero))
def mfour := succ mthree

-- When you implement lt_mnat correctly,
-- the following tests should all give the 
-- right answers.

#reduce lt_mnat mzero mzero
#reduce lt_mnat mzero mtwo
#reduce lt_mnat mtwo mtwo
#reduce lt_mnat mtwo zero
#reduce lt_mnat mtwo mthree
#reduce lt_mnat mthree mtwo 

/- [10 points]
#1B. Implement an mnat multiplication
function by completing the following
definition. Hint: use the distributive
law to figure out how to write the
recursive case. What is (1 + n') * m? 
-/

def mult_mnat : mnat → mnat → mnat
| zero _ := zero
| (succ n') m := _

-- When you succeed you should get
-- the right answers for these tests
#reduce mult_mnat mzero mzero
#reduce mult_mnat mzero mthree
#reduce mult_mnat mthree mzero
#reduce mult_mnat mtwo mthree
#reduce mult_mnat mthree mtwo
#reduce mult_mnat mthree mthree


/- [10 points]
#1C. Implement the factorial function
using the mnat type. Call your function
fac_mnat. Give a definition by cases using
recursion, in the style of the preceding
examples.
-/

-- Your code here


-- Add test cases for zero, one, and
-- some larger argument values and check
-- that you're getting the right answers.

-- Here


/-
#2. Inductive data type definitions.

For this problem, you will extend a 
very simple "list of natural numbers"
abstract data type. You will first read
and understand a list_nat data type we
give you, then you will define several
functions that operate on values of
this type.
-/

/-
The following inductive definition
defines a set of terms. The base case is
nil, representing an empty list of mnat.
The cons constructor on the other hand
takes an mnat (let's call it h) and any
list of mnats (call it t) and returns the
term, (cons h t), which we interpret as a
one-longer list with h at its "head" and
the one-smaller list, l, as its "tail"). 
-/
inductive list_mnat : Type
| nil
| cons : mnat → list_mnat → list_mnat

open list_mnat 

-- Here are two list definitions using
-- our new data type

-- representation of an empty list
def empty_list := nil

-- representation of the list [1, 2, 3]
def one_two_three := 
    cons 
        mone 
        (cons 
            mtwo 
            (cons 
                mthree
                nil
            )
        )

/-
2A. [10 points]

Define three_four to represent the
list [3, 4].
-/

-- Here


/-
#2B. [10 points]

Implement a predicate function,
is_empty, that takes a list_mnat and
returns tt if an only if it's empty,
otherwise ff. Remember once again
that a "predicate" function is one
that returns a Boolean true or false
value depending on whether the argument
to which it is applied has a specified
property or not. Here the property is
that of being an empty list, or not.
-/

-- Your answer here


/-
#2C. [10 points]

Implement a prepend_mnat function
that takes an mnat, h, and a list_mnat,
t, and that returns a new list with h
as the value at the head of the list
and t as the "rest" of the new list (its
"tail").
-/

-- Your answer here


/-
#2D. [10 points]

Define a recursive "length_mnat" function
that takes any list_mnat and returns its
length.
-/



/-
2F. [Extra Credit]

Implement an append_mnat function. 
It takes two list_mnat values and returns
a new one, which is the first appended
to (and followed by) the second. So, for
example, the list [1, 2] appended to the
list [3, 4, 5] should return the list,
[1, 2, 3, 4, 5]. Of course you won't be
using this nice list notation, just the
constructors we've defined.
-/

-- Your answer here


/-
Add tests where the first list is nil and
not nil, and make sure you're getting the
right answers.
-/ 


/-
#3. Higher-Order Functions

Lean's library-provided polymorphic list type
is implemented in essentially the same way as
the list_mnat type you used in the preceding
questions. The main difference is that the
type of elements in a Lean list is given as 
a parameter to the "list" type. We covered 
the use of Lean's (polymorphic) list type
in class. Review your notes if necessary.
-/

/-
3A. [10 points] Provide an implementatation of
a function, map_pred. This function will take
as its arguments (1) any predicate function of
type ℕ → bool, (2) any list of natural numbers
(of type "list nat"). It will then return a new
list in which each ℕ value in the given list is
replaced by true (tt) if the predicate returns
true for that value, and otherwise by false (ff).

For example, if the predicate function returns
true if and only if its argument is zero, then
applying map to this function and to the list
[0,1,2,0,1,0] must return [tt,ff,ff,tt,ff,tt].


Test your code by using #eval or #reduce to evaluate
an expression in which map_pred is applied to 
such an "is_zero" predicate function and to the
list 0,1,2,0,1,0]. Express the predicate function
as a lambda abstraction within the #eval command.
-/

-- Answer here


/-
3B. [5points] Implement a function, reduce_or, 
that takes as its argument a list of Boolean values 
and that reduces the list to a single Boolean value: 
tt if there is at least one true value in the list,
otherwise ff. Note: the Lean libraries provide the
function "bor" to compute "b1 or b2", where b1 and
b2 are Booleans.
-/

-- example
#reduce bor tt tt

-- Answer here

/-
3C. [5 points] Implement a function, reduce_and,
that takes as its argument a list of Boolean values 
and that reduces the list to a single Boolean value: 
tt if every value in the list is true, otherwise ff.
-/

-- Note: band implements the Boolean "and" function
#reduce band tt tt

-- Answer here


/-
3D. [10 points] Define a function, all_zero, that 
takes a list of mnat values and returns true if and 
only if they are all zero. Express your answer using 
only the map and reduce functions.
-/


-- Answer here



/-
This is the end of the homework. Please 
be sure to save your file before uploading
then check that you uploaded correctly. We
cannot accept work submitted incorrectly
or late, so take a minute to be sure you
got it right. Thank you!
-/