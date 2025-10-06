module Sessions.Types.Local

import public Decidable.Equality

import public Data.SnocList
import public Data.SnocList.Elem

import public Extra

import public Sessions.Types.Base
import public Sessions.Types.Common

mutual
  public export
  data Branch : Role.Context -> Fix.Context -> Type
    where
      B : (l : String)
       -> (t : Base)
       -> (k : Local rs fs)
            -> Branch rs fs

  public export
  data Local : Role.Context
            -> Fix.Context
            -> Type
    where
      Stop : Local rs fs
      Call : {n : _}
          -> AtIndex MkFix fs n
          -> Local rs fs
      Rec : Local rs (fs :< MkFix)
         -> Local rs fs
      Comm : CTy
          -> AtIndex r rs n
          -> List (Branch rs fs)
          -> Local rs fs

-- [ EOF ]
