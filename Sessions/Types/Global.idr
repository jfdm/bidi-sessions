module Sessions.Types.Global

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
       -> (k : Global rs fs)
            -> Branch rs fs

  public export
  data Global : Role.Context
             -> Fix.Context
             -> Type
    where
      Stop : Global rs fs
      Call : {n : _}
          -> AtIndex MkFix fs n
          -> Global rs fs
      Rec : Global rs (fs :< MkFix)
         -> Global rs fs
      Choice : (x : AtIndex s rs n)
            -> (y : AtIndex r rs m)
            -> EqualNot x y
            -> List (Branch rs fs)
            -> Global rs fs

-- [ EOF ]
