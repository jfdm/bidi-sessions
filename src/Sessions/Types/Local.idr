module Sessions.Types.Local

import public Decidable.Equality

import public Data.SnocList
import public Data.SnocList.Elem

import public Extra

import public Sessions.Types.Base
import public Sessions.Types.Common

%default total

public export
Local : Role.Context
     -> Fix.Context
     -> Type
Local = Protocol LOCAL

public export
Branch : Role.Context
      -> Fix.Context
      -> Type
Branch = Branch Local

-- [ EOF ]
