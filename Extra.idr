module Extra

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

namespace SnocList

namespace List

  public export
  data Shape : (xs,ys : List a) -> Type
    where
      End : Shape [] []
      LH : Shape (x::xs) Nil
      RH : Shape Nil (y::ys)
      B : Shape (x::xs) (y::ys)

  export
  shape : (xs, ys : List a ) -> Shape xs ys
  shape [] [] = End
  shape [] (x :: xs) = RH
  shape (x :: xs) [] = LH
  shape (x :: xs) (y :: ys) = B

  namespace Elem
    noHR : (the (Elem x (xs :< x)) (Here)) = the (Elem y (ys :< y')) (There z) -> Void
    noHR Refl impossible

    noRH : the (Elem y (ys :< y')) (There z) = (the (Elem x (xs :< x)) (Here)) -> Void
    noRH Refl impossible

    export
    decEq : (ix : SnocList.Elem.Elem x xs)
         -> (yx : SnocList.Elem.Elem y xs)
         -> Dec (ix = yx)
    decEq Here Here
      = Yes Refl
    decEq Here (There z)
      = No noHR
    decEq (There z) Here
      = No noRH
    decEq (There z) (There y) with (decEq z y)
      decEq (There z) (There z) | (Yes Refl)
        = Yes Refl
      decEq (There z) (There y) | (No contra)
        = No (\case Refl => contra Refl)

namespace SnocList

  namespace AtIndex

    public export
    data AtIndex : a -> SnocList a -> Nat -> Type where
      H : (prf : x = y) -> AtIndex x (sx :< y) 0
      T : AtIndex x sx   n
       -> AtIndex x (sx :< y) (S n)


    heavyRight : H Refl = T z -> Void
    heavyRight Refl impossible

    heavyLeft : T z = H Refl -> Void
    heavyLeft Refl impossible

    export
    decEq : (idx : AtIndex x sx n)
         -> (idy : AtIndex y sx a)
         -> Dec (idx = idy)
    decEq (H Refl) (H Refl) = Yes Refl
    decEq (H Refl) (T z)
      = No heavyRight
    decEq (T z) (H Refl) = No heavyLeft
    decEq (T z) (T w) with (decEq z w)
      decEq (T z) (T z) | (Yes Refl) = Yes Refl
      decEq (T z) (T w) | (No no)
        = No (\case Refl => no Refl)

    Uninhabited (AtIndex x Lin n) where
      uninhabited H impossible
      uninhabited (T y) impossible


    export
    index : (xs : SnocList a)
         -> (idx  : Nat)
                 -> Dec (DPair a (\x => AtIndex x xs idx))
    index [<] _ = No (\p => void (absurd (snd p)))

    index (sx :< x) 0 = Yes (x ** H Refl)
    index (sx :< x) (S k) with (index sx k)
      index (sx :< x) (S k) | (Yes ((fst ** snd))) = Yes (fst ** T snd)
      index (sx :< x) (S k) | (No contra)
        = No (\case (fst ** (T y)) => contra (fst ** y))

    export
    lookup : DecEq a
          => (xs : SnocList a)
          -> (x  : a)
                 -> Dec (DPair Nat (AtIndex x xs))
    lookup [<] n
      = No (\p => void (absurd (snd p)))

    lookup (sx :< y) x with (decEq x y)
      lookup (sx :< x) x | (Yes Refl)
        = Yes (0 ** H Refl)
      lookup (sx :< y) x | (No no) with (lookup sx x)
        lookup (sx :< y) x | (No no) | (Yes ((fst ** snd)))
          = Yes (S fst ** T snd)
        lookup (sx :< y) x | (No no) | (No contra)
          = No (\case (Z ** H Refl) => no Refl
                      (((S n) ** (T z))) => contra (n ** z))

    export
    unique : (this : AtIndex x xs n)
          -> (that : AtIndex y xs n)
                  -> Equal x y
    unique (H Refl) (H Refl) = Refl
    unique (T z) (T w) = unique z w



  namespace Lookup
    public export
    data Elem : Pair a b -> SnocList (a,b) -> Type where
      Here : (prfN : Equal x y)
          -> (prfT : Equal a b)
                  -> Lookup.Elem (x,a) (tesr :< (y,b))

      There : (contraN : Equal x y -> Void)
           -> (later   : Lookup.Elem (x,a) tesr)
                      -> Lookup.Elem (x,a) (tesr :< (y,b))


    public export
    data Equal : Lookup.Elem a xs
              -> Lookup.Elem b xs
              -> Type
      where
        H : Equal (Here Refl Refl)
                  (Here Refl Refl)
        T : Lookup.Equal lx ly
         -> Equal (There nx lx) (There ny ly)

    noEqHR : Lookup.Equal (Here Refl Refl) (There contraN later) -> Void
    noEqHR H impossible
    noEqHR (T x) impossible

    noEqRH : Lookup.Equal (There contraN later) (Here Refl Refl) -> Void
    noEqRH H impossible
    noEqRH (T x) impossible

    export
    decEq : (xs : Lookup.Elem a zs)
         -> (ys : Lookup.Elem b zs)
               -> Dec (Lookup.Equal xs ys)
    decEq (Here Refl Refl) (Here Refl Refl)
      = Yes H
    decEq (Here Refl Refl) (There contraN later)
      = No noEqHR

    decEq (There contraN later) (Here Refl Refl)
      = No noEqRH
    decEq (There nx x) (There ny y) with (decEq x y)
      decEq (There nx x) (There ny y) | (Yes prf) = Yes (T prf)
      decEq (There nx x) (There ny y) | (No no)
        = No (\case (T z) => no z)


    Uninhabited (Lookup.Elem (k,v) Lin) where
      uninhabited (Here prfN prfT) impossible
      uninhabited (There contraN later) impossible

    Uninhabited (DPair b (\type => Lookup.Elem (name, type) Lin)) where
      uninhabited ((fst ** snd)) = absurd snd

    notInRest : (name = x -> Void)
             -> (DPair b (\type => Lookup.Elem (name, type) sx) -> Void)
             -> DPair b (\type => Lookup.Elem (name, type) (sx :< (x, type')))
             -> Void
    notInRest f g (MkDPair type' (Here Refl Refl)) = f Refl
    notInRest f g (MkDPair fst (There contraN later)) = g (_ ** later)

    export
    lookup : DecEq a
          => DecEq b
          => (ctxt : SnocList (a,b))
          -> (name : a)
                  -> Dec (type ** Lookup.Elem (name,type) ctxt)
    lookup Lin name = No absurd
    lookup (sx :< (x,type') ) name with (decEq name x)
      lookup (sx :< (name,type')) name | (Yes Refl) = Yes (MkDPair type' (Here Refl Refl))
      lookup (sx :< (x,type')) name | (No contra) with (lookup sx name)
        lookup (sx :< (x,type')) name | (No contra) | (Yes (MkDPair fst snd))
          = Yes (_ ** There contra snd)
        lookup (sx :< (x,type')) name | (No contra) | (No f)
          = No (notInRest contra f)

    export
    unique : (this : Lookup.Elem (x,a) ctxt)
          -> (that : Lookup.Elem (x,b) ctxt)
                  -> Equal a b
    unique (Here Refl Refl) (Here Refl Refl)
      = Refl
    unique (There no _) (Here prf _)
      = absurd (no prf)

    unique (Here prf _) (There no _)
      = absurd (no prf)

    unique (There _ ltrA) (There _ ltrB) = unique ltrA ltrB


{-
    noHR : (the (Elem x (xs :< x)) (Here)) = the (Elem y (ys :< y')) (There z) -> Void
    noHR Refl impossible

    noRH : the (Elem y (ys :< y')) (There z) = (the (Elem x (xs :< x)) (Here)) -> Void
    noRH Refl impossible

-}
-- [ EOF ]
