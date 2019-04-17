infix 30 _≡_

data _≡_ {w : Set} (_x : w) : w -> Set where
  refl_eq : _x ≡ _x

{-# BUILTIN EQUALITY _≡_ #-}

{-Proofs here are very close of church encoding dependent typed proved in coq-} 

data A_nat (A : Set) (f : A -> A) : A -> Set where
  As : ∀ {x : A} ->  A_nat _ f x -> A_nat _ f (f x)
  Azero : ∀ {x : A} -> A_nat _  f x
 
fzero : {T : Set} -> T -> (T -> T) -> T
fzero x f = x

sn : {T : Set} -> (T -> (T -> T) -> T) -> T -> (T -> T) -> T
sn f x a = f (a x) a

ind_r : {B : Set} (f : B -> B) (A : B) -> A_nat _ f A -> B
ind_r y c k = c

one : {X : Set} -> X -> (X -> X) -> X
one t w = sn fzero t w

A_one : {X : Set} (x : X) (f : X -> X) -> A_nat _ f (f x)
A_one f x = As Azero 

a_one_eq_one : ∀ {A : Set} (t : A) (k : A -> A) -> one t k ≡ ind_r _ _ (A_one t k)
a_one_eq_one y z = refl_eq

n_ : {A : Set} (f : A -> A) (c : A) -> A_nat _ f c -> A
n_ _ x Azero = x 
n_ _ _ (As k) = n_ _ _  k

data n_corresq {T : Set} {G : T -> T}  : ∀ (x : T) -> A_nat T G x -> (T -> (T -> T) -> T) -> Set where
  eq_correspondence : {q : T -> (T -> T) -> T} {y : T} {d : A_nat _ G y} -> (ind_r _ _ d) ≡ q (n_ _ _ d) G -> n_corresq _ d q -> n_corresq _ (As d) (sn q)
  base_correspondence : ∀ (y : T) (b : T -> (T -> T) -> T) -> ind_r G y Azero ≡ b (n_ G y Azero) G -> n_corresq (G y) (As Azero) (sn fzero)

sn_nat : ∀ {A : Set} {v' : A} {f' : A -> A} (n : A_nat _  f' v') -> (A -> (A -> A) -> A)
sn_nat Azero = fzero
sn_nat (As k) = sn (sn_nat k)

puref' : ∀ {A : Set} {x : A} {f : A -> A} -> (f x ≡ f x) -> x ≡ x
puref' k = refl_eq

eq_homo_pred : ∀ {A : Set} {f : A -> A} {x : A} {n : A_nat _ f x} {y : A} -> f (sn_nat n y f) ≡ (sn_nat (As n) y f) -> (sn_nat n y f) ≡ (sn_nat n y f)
eq_homo_pred H' rewrite H' = refl_eq

eq_homo_succ : ∀ {A : Set} {f : A -> A} {x : A} (n : A_nat _ f x) (y : A) -> ((sn (sn_nat n)) y f) ≡ f (sn_nat n y f) 
eq_homo_succ Azero  y = refl_eq
eq_homo_succ {_} {f} {_} (As k) H = eq_homo_succ k (f H)

eq_homo_succ' : ∀ {A : Set} {f : A -> A} {x : A} (n : A_nat _ f x) (y : A) -> ((sn (sn_nat n)) y f) ≡ (sn_nat n (f y) f)
eq_homo_succ' Azero  y = refl_eq
eq_homo_succ' {_} {f} {_} (As k) H = eq_homo_succ' k (f H)

homo_succ_by_hyptosis' : ∀ {A : Set} {f : A -> A} {x : A} (n : A_nat _ f x) (y : A) -> ((sn (sn_nat n)) y f) ≡ (sn_nat n (f y) f) -> ((sn (sn (sn_nat n))) y f) ≡ (sn_nat n (f (f y)) f)
homo_succ_by_hyptosis'  Azero y H' rewrite H'  = refl_eq
homo_succ_by_hyptosis' {_} {f} {_} (As k) v  H = homo_succ_by_hyptosis' k (f v) (eq_homo_succ' k (f v))

simpl_sn_succ : ∀ {A : Set} {f : A -> A} {x : A} (n : A_nat _ f x) (y : A) -> ((sn (sn_nat n)) y f) ≡ (sn_nat n (f y) f)
simpl_sn_succ _ _ = refl_eq

homo_nat : ∀ {A : Set} {f : A -> A} {x : A} (n : A_nat _ f x) (y : A) -> (sn_nat (As n) y f) ≡ f (sn_nat n y f)
homo_nat x v' = eq_homo_succ x v'

simpl_As : ∀ {A : Set} {f : A -> A} {x : A} (k : A_nat _ f x) (y : A) -> (sn_nat (As k) y f) ≡ f (sn_nat k y f) -> (f (sn_nat k (f y) f)) ≡ (f (f (sn_nat k y f)))
simpl_As n y eq' rewrite eq' = refl_eq

homo_fAsapp : ∀ {Y : Set} {f : Y -> Y} {x : Y} (n : A_nat _ f x) (y : Y) -> (sn_nat (As (As n)) y f) ≡ f (f (sn_nat n y f))
homo_fAsapp {_} {f} {_}  k y with (sn_nat (As (As k)) y f)          | homo_nat (As k) y
homo_fAsapp {_} {f} {_} k y'    | (. (f  (sn_nat (As k) y' f)))     | refl_eq              = simpl_As k y' (homo_nat k y')  

hypothesis_induc_nat : ∀ {A : Set} {x' : A} {f' : A -> A} (n : A_nat _ f' x') -> (sn_nat (As n) (n_ _ _  n) f') ≡ (f' (sn_nat n (n_ _ _ n) f'))
hypothesis_induc_nat Azero = refl_eq
hypothesis_induc_nat {_} {_} {f'} (As {v'} d) = homo_nat (As d) (n_ f' (f' v') (As d))
     
continuation_nat_app : ∀ {Y : Set} {f : Y -> Y} {x : Y} (n : A_nat _ f x) (y : Y) -> ((sn_nat (As (As n)) y f)) ≡ f (f (sn_nat n  y  f))
continuation_nat_app {_} {f} {k}  Azero V  = homomorphism_nat {_} {f} {_} (As {_} {f} {k}  Azero) V
  where
    homomorphism_nat = homo_nat
continuation_nat_app {_} {f} {_} (As {w} k') v'  = (homo_fAsapp (As k') v')

minimum_value_as_eq : {Y : Set} {f : Y -> Y} {x : Y} (n : A_nat _ f x) -> (n_ _ _ n ≡ n_ _ _ (As n))
minimum_value_as_eq Azero = refl_eq
minimum_value_as_eq (As k) = minimum_value_as_eq k

case0isalways_eq : {Y : Set} {f : Y -> Y} {x : Y} (n : A_nat _ f x) -> (sn_nat n (n_ _ _ (As n)) f ≡ sn_nat n (n_ _ _ n) f)
case0isalways_eq _ = refl_eq

n_correspondence : ∀ {A : Set} {f' : A -> A} {v' : A} (n : A_nat _  f' v') -> n_corresq _ (As n) (sn_nat (As n))
n_correspondence {_} {f'} {v'} Azero = base_correspondence v' fzero refl_eq
n_correspondence {_} {f'} {_} (As {v'} k')  = eq_correspondence (ind_nat_eq (As k')) (n_correspondence k')
  where
     n_is_v' : ∀ {A : Set} {f' : A -> A} {v' : A} (n : A_nat _ f' v') (d : A) (H : d ≡ v') -> (n ≡ Azero) -> (v' ≡ ((sn_nat n) d f'))
     n_is_v' _ _ p refl_eq rewrite p = refl_eq   
     ind_nat_eq : ∀ {A : Set} {f' :  A -> A} {x' : A} (n : A_nat _ f' x') -> x' ≡ ((sn_nat n) (n_ _ _ n) f')
     ind_nat_eq {_} {f'} {v'} Azero =
       let n_zero_lemma : ∀ {A : Set} {f' :  A -> A} {v' : A} -> ((n_ f' v' Azero) ≡ v')
           n_zero_lemma = refl_eq 
       in (n_is_v' {_} {f'} {v'} Azero v' (n_zero_lemma {_} {f'} {v'}) refl_eq)
     ind_nat_eq {_} {f} (As {v} k) = (lemma_to_apply_nat_homo k (ind_nat_eq k))
      where
         lemma_to_apply_nat_homo : ∀ {A : Set} {f' : A -> A} {x' : A} (n : A_nat _ f' x') -> x' ≡ (sn_nat n (n_ _ _ n) f') -> f' x' ≡ (sn_nat (As n) (n_ _ _ (As n)) f')
         lemma_to_apply_nat_homo {_} {f'} Azero H' rewrite H' = refl_eq
         lemma_to_apply_nat_homo {_} {f'} (As {x} k) H' rewrite H' = symmetric _ _  (hypothesis_induc_nat (As k))
           where
             symmetric : ∀ {A : Set} (x y : A) -> (x ≡ y) -> (y ≡ x)
             symmetric _ _  k rewrite k = refl_eq
