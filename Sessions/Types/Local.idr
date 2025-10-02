module Sessions.Types.Local

import public Decidable.Equality

import public Data.SnocList
import public Data.SnocList.Elem

import public Sessions.Types.Base
import public Sessions.Types.Common

mutual
  public export
  data Branch : SnocList Role -> SnocList Fix -> Type
    where
      B : (l : String)
       -> (t : Base)
       -> (k : Local rs fs)
            -> Branch rs fs

  public export
  data Local : SnocList Role
            -> SnocList Fix
            -> Type
    where
      Stop : Local rs fs
      Call : Elem   f fs
          -> Local rs fs
      Rec : (f : Fix)
         -> Local rs (fs :< f)
         -> Local rs fs
      Comm : CTy
          -> Elem r rs
          -> List (Branch rs fs)
          -> Local rs fs

-- [ EOF ]
