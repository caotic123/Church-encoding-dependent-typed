# The-Dependent-Church-Encoding

# Main idea 
This work is a collection of proofs of correspondence dependent data type of classical church codification.
Of course, some codifications were changed to a better look of representable data.

For example :

Naturals numbers are well-know enconding like : 

```haskell
n x = x
k c x = c x
```

To this below :
```haskell
n x f = f x
k f x a = f (a x) a
```

'Cause to prove in second definition it's observable that a function f is applyed n times in any x, so to prove that, just check (f ... (f x)) is equal to (f ... (f x)) of that's
structures (church encoding x (co) inductive data) is more easy.

The main idea is proof that correspondence, so to prove some relevant theories in dependent data and certificate that church codifications have the same properties.

# Simple example

In any functional language it's possible encoding typed church encodifications, for example :

Define a boolean type as two function : one that take two arguments and return the first and ~one function that return the second function.
So, one = true and ~one = false.

True = λx.λy. x
False = λx.λy. y

With a simple definition of algebraic data type we can code the same effect in this way :

```haskell
data bool = True | False.
```

Let's suppose that the core of haskell language is consistent and don't support partial function:
The unique effect that you can in agdt codification and the church codification is the same.

Let's suppose bool_possibility as :

```haskell
bool of
  True -> exp_true
  False -> exp_false
  
-- or even

cond True = exp_true
cond False = exp_false
```

If you check it's the same you only have in the church codification :
```
check f x y = f x
check True x y = (λx.λy.x) exp_true exp_false
check False x y = (λx.λy.y) exp_true exp_true
```


So bool_possibility of check and bool matching is the same, *of course the definition used in this work it's not agdt boolean, however both are correspondent too*.


# More works...

This project is a extension of :

https://github.com/caotic123/BrainLambda (A brainfuck codification in lambda calculus)
https://github.com/caotic123/Grr-Programming-Language (A pure textual language that someway encode lambda terms)

If you have a question or just want to tell something just text me : camposferreiratiago@gmail.com, or any way you found contact doesn't matter :)