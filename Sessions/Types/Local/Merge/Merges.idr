module Sessions.Types.Local.Merge.Merges

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import public Extra

import Sessions.Types.Local

%default total

public export
data Merges : (how : (a,b,c : Local rs fs) -> Type)
           -> (xs : List (Local rs fs))
           -> (z   :       Local rs fs)
           -> Type
  where
    Last : Merges how [x] x
    Next : {z,q : _}
        -> Merges how xs z
        -> how x z q
        -> Merges how (x::xs) q

Uninhabited (Merges how [] z) where
  uninhabited Last impossible
  uninhabited (Next x y w) impossible

export
unique : {0 how : (a,b,c : Local rs fs) -> Type}
      -> (f : {0 a,b,c,d : Local rs fs}
           -> (  this : how a b c)
           -> (  that : how a b d)
           -> c === d)
      -> Merges how xs a
      -> Merges how xs b
      -> a === b
unique f Last Last = Refl
unique f (Next xs xc) (Next ys zq) with (unique f xs ys)
    unique f (Next xs xq) (Next ys yq) | Refl with (f xq yq)
      unique f (Next xs xq) (Next ys yq) | Refl | Refl = Refl

finalMergeFails : (u : {0 a,b,c,d : Local rs fs}
                    -> (  this : how a b c)
                    -> (  that : how a b d)
                    -> c === d)
               -> (DPair (Local rs fs) (how x that) -> Void)
               -> Merges how (y :: xs) that
               -> DPair (Local rs fs) (Merges how (x :: (y :: xs)))
               -> Void
finalMergeFails u f pXS (fst ** (Next pXS' w)) with (unique u pXS pXS')
  finalMergeFails u f pXS (fst ** (Next pXS' w)) | Refl = f (fst ** w)

export
merge : (f : (a,b : Local rs fs) -> Dec (DPair (Local rs fs)
                                                 (how a b)))
     -> (u : {0 a,b,c,d : Local rs fs}
           -> (  this : how a b c)
           -> (  that : how a b d)
           -> c === d)
     -> (xs : List (Local rs fs))
           -> Dec (DPair (Local rs fs) (Merges how xs))
merge f _ []
  = No $ \case (ty ** prf) => absurd prf

merge f _ (x :: [])
  = Yes (x ** Last)

merge f u (x :: (y :: xs)) with (merge f u (y::xs))
  merge f u (x :: (y :: xs)) | (Yes (that ** pThat)) with (f x that)
    merge f u (x :: (y :: xs)) | (Yes (that ** pThat)) | (Yes (ty ** prf))
      = Yes (ty ** Next pThat prf)
    merge f u (x :: (y :: xs)) | (Yes (that ** pThat)) | (No no)
      = No (finalMergeFails u no pThat)

  merge f u (x :: (y :: xs)) | (No no)
    = No $ \case (ty ** Next x xs) => no (_ ** x)

-- [ EOF ]
