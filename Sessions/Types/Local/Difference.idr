module Sessions.Types.Local.Difference

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import Sessions.Types.Local

namespace Branch

  public export
  data Diff : (x,y : Branch rs fs)
           -> Type
    where
      D : Not (lx = ly)
       -> Diff (B lx tx kx)
               (B ly ty ky)


  areSame : Diff (B lx _ _) (B lx _ _) -> Void
  areSame (D f) = f Refl

  export
  diff : (x,y : Branch rs fs) -> Dec (Diff x y)
  diff (B lx _ _) (B ly _ _) with (Equality.decEq lx ly)
    diff (B lx _ _) (B lx _ _) | (Yes Refl) = No areSame
    diff (B lx _ _) (B ly _ _) | (No contra)
      = Yes (D contra)


namespace Branches

  namespace Branch

    public export
    data Diff : (x  :      (Branch rs fs))
             -> (ys : List (Branch rs fs))
             -> Type
      where
        Empty : Diff x Nil
        There : Diff x  y
             -> Diff x     ys
             -> Diff x (y::ys)

    export
    diff : (x  : Branch rs fs)
        -> (ys : List $ Branch rs fs)
              -> Dec (Diff x ys)
    diff x []
      = Yes Empty
    diff x (y :: ys) with (diff x y)
      diff x (y :: ys) | (Yes prf) with (diff x ys)
        diff x (y :: ys) | (Yes pH) | (Yes pT)
          = Yes (There pH pT)

        diff x (y :: ys) | (Yes pH) | (No contra)
          = No (\case (There _ pT) => contra pT)

      diff x (y :: xs) | (No contra)
        = No (\case (There pH pT) => contra pH)

  public export
  data Diff : (xs  : List (Branch rs fs))
           -> (ys  : List (Branch rs fs))
           -> (zs  : List (Branch rs fs))
                  -> Type
    where
      EndL : Diff Nil ys Nil
      Here : Diff x ys
          -> Diff xs ys zs
          -> Diff (x::xs) ys (x::zs)

      Skip : Not (Diff x ys)
          -> Diff xs      ys zs
          -> Diff (x::xs) ys zs

  export
  diff : (xs,ys : List (Branch rs fs))
               -> DPair (List (Branch rs fs))
                        (Diff xs ys)
  diff [] ys
    = ([] ** EndL)

  diff (x :: xs) ys with (diff x ys)
    diff (x :: xs) ys | with_pat with (diff xs ys)
      diff (x :: xs) ys | (Yes prfH) | (zs ** prfT)
        = (x :: zs ** Here prfH prfT)
      diff (x :: xs) ys | (No contra) | (zs ** prfT)
        = (zs ** Skip contra prfT)

  export
  uniques : Diff xs ys as
         -> Diff xs ys bs
        -> as === bs
  uniques EndL EndL
    = Refl
  uniques (Here x xs) (Here y ys) with (uniques xs ys)
    uniques (Here x xs) (Here y ys) | Refl = Refl

  uniques (Here x xs) (Skip f y) = void (absurd $ f x)

  uniques (Skip f x) (Here y ys) = void $ absurd (f y)

  uniques (Skip f x) (Skip g y) with (uniques x y)
    uniques (Skip f x) (Skip g y) | Refl = Refl

-- [ EOF ]
