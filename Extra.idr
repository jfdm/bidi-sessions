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
  namespace Lookup
    public export
    data Elem : Pair a b -> SnocList (a,b) -> Type where
      Here : (prfN : Equal x y)
          -> (prfT : Equal a b)
                  -> Lookup.Elem (x,a) (tesr :< (y,b))

      There : (contraN : Equal x y -> Void)
           -> (later   : Lookup.Elem (x,a) tesr)
                      -> Lookup.Elem (x,a) (tesr :< (y,b))

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

-- [ EOF ]
