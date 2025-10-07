module Sessions.Types.Local.Merge.Projection.Merges

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import public Extra

import Sessions.Types.Local
import Sessions.Types.Local.Merge.Projection

%default total

public export
data Merges : (xs : List (Local rs fs))
           -> (z   :       Local rs fs)
           -> Type
  where
    Last : Merges [x] x
    Next : {z,q : _}
        -> Merges xs z
        -> Projection.Merge x z q
        -> Merges (x::xs) q

Uninhabited (Merges [] z) where
  uninhabited Last impossible
  uninhabited (Next x y w) impossible

export
unique : Merges xs a
      -> Merges xs b
      -> a === b
unique Last Last = Refl
unique (Next xs xc) (Next ys zq) with (unique xs ys)
    unique (Next xs xq) (Next ys yq) | Refl with (unique xq yq)
      unique (Next xs xq) (Next ys yq) | Refl | Refl = Refl

finalMergeFails : (DPair (Local rs fs) (Merge x z) -> Void) -> Merges (y :: xs) z
               -> DPair (Local rs fs) (Merges  (x :: (y :: xs))) -> Void
finalMergeFails f w (fst ** (Next v s)) with (unique w v)
  finalMergeFails f w (fst ** (Next v s)) | Refl = f (fst ** s)

export
merge : (xs : List (Local rs fs))
            -> Dec (DPair (Local rs fs) (Merges xs))
merge []
  = No $ \case (fst ** snd) => absurd snd

merge (x :: [])
  = Yes (x ** Last)

merge (x :: y :: xs) with (merge (y::xs))
  merge (x :: y :: xs) | (Yes (z ** pZ)) with (merge x z)
    merge (x :: y :: xs) | (Yes (z ** pZ)) | (Yes (fst ** snd))
      = Yes (fst ** Next pZ snd)
    merge (x :: y :: xs) | (Yes (z ** pZ)) | (No no)
      = No (finalMergeFails no pZ)
  merge (x :: y :: xs) | (No contra)
    = No $ \case ((fst ** (Next z w))) => (contra (_ ** z))

-- [ EOF ]
