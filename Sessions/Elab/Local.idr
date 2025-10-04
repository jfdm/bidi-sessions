module Sessions.Elab.Local

import Sessions.Types.Local
import Sessions.Types.Local.Subset
import Sessions.Types.Local.Merge.Synthesis
import Sessions.AST

namespace Synth
  namespace Local
    namespace Branches
      public export
      data Local : (how : (rs : SnocList Role)
                       -> (fs : SnocList Fix)
                       -> (tm : Local)
                       -> (ty : Local rs fs)
                             -> Type)
                -> (rs  : SnocList Role)
                -> (fs  : SnocList Fix)
                -> (tms : List (String, Base, Local))
                -> (tys : List (Branch rs fs))
                       -> Type
        where
          End : Local how rs fs Nil Nil
          Ext : {0 how : (rs : SnocList Role)
                      -> (fs : SnocList Fix)
                      -> (tm : Local)
                      -> (ty : Local rs fs)
                            -> Type}
             -> (head : how rs fs ktm kty)
             -> (next : Local how rs fs tms tys)
                     -> Local how rs fs ((l,b,ktm)::tms) (B l b kty :: tys)

      export
      synth : {0 how : (rs : SnocList Role)
                    -> (fs : SnocList Fix)
                    -> (tm : Local)
                    -> (ty : Local rs fs)
                          -> Type}
           -> (f : (rs : SnocList Role)
                -> (fs : SnocList Fix)
                -> (tm : Local)
                      -> Dec (DPair (Local rs fs) (how rs fs tm)))
           -> (rs  : SnocList Role)
           -> (fs  : SnocList Fix)
           -> (tms : List (String, Base, Local))
                  -> Dec (DPair (List (Branch rs fs))
                                (Branches.Local how rs fs tms))
      synth f rs fs []
        = Yes ([] ** End)

      synth f rs fs ((l,b,x) :: xs) with (f rs fs x)
        synth f rs fs ((l,b,x) :: xs) | (Yes (ty ** tm)) with (synth f rs fs xs)
          synth f rs fs ((l,b,x) :: xs) | (Yes (ty ** tm)) | (Yes (tys ** tms))
            = Yes (B l b ty :: tys ** Ext tm tms)
          synth f rs fs ((l,b,x) :: xs) | (Yes (ty ** tm)) | (No no)
            = No (\case ((B l b kty :: tys) ** (Ext head next)) => no (tys ** next))

        synth f rs fs ((l,b,x) :: xs) | (No noH)
          = No (\case ((B l b kty :: tys) ** (Ext head next)) => noH (kty ** head))

    public export
    data Local : (rs : SnocList Role)
              -> (fs : SnocList Fix)
              -> (tm : Local)
              -> (ty : Local rs fs)
                    -> Type
      where
        End : Local rs fs End Stop
        Call : (idx : AtIndex (MkFix f) fs n)
                   -> Local rs fs (Call f) (Call idx)

        Rec : Local rs (fs :< (MkFix f)) kast kty
           -> Local rs fs (Rec f kast) (Rec f kty)

        Comm : (idx : Elem (MkRole r) rs)
            -> Local Local rs fs tms tys
            -> Local rs fs (Comm cty r tms) (Comm cty idx tys)

    export
    synth : (rs : SnocList Role)
         -> (fs : SnocList Fix)
         -> (tm : Local)
               -> Dec (DPair (Local rs fs)
                             (Local rs fs tm))
    synth rs fs End
      = Yes (Stop ** End)

    synth rs fs (Call str) with (lookup fs (MkFix str))
      synth rs fs (Call str) | (Yes (n ** prf))
        = Yes (Call prf ** Call prf)
      synth rs fs (Call str) | (No no)
        = No (\case ((Call idx) ** (Call idx)) => no (_ ** idx) )

    synth rs fs (Rec str k) with (synth rs (fs :< (MkFix str)) k)
      synth rs fs (Rec str k) | (Yes (kty ** prf))
        = Yes (Rec str kty ** Rec prf)
      synth rs fs (Rec str k) | (No no)
        = No (\case ((Rec str kty) ** (Rec x)) => no (kty ** x))

    synth rs fs (Comm cty r bs) with (isElem (MkRole r) rs)
      synth rs fs (Comm cty r bs) | (Yes ridx) with (synth synth rs fs bs)
        synth rs fs (Comm cty r bs) | (Yes ridx) | (Yes (tys ** tms))
          = Yes (Comm cty ridx tys ** Comm ridx tms)
        synth rs fs (Comm cty r bs) | (Yes ridx) | (No no)
          = No (\case ((Comm cty idx tys) ** (Comm idx x)) => no (tys ** x))

      synth rs fs (Comm cty r bs) | (No no)
        = No (\case (Comm cty idx tys ** Comm idx x) => no idx)

  namespace Local

    uniques : Local Local rs fs tms a
           -> Local Local rs fs tms b
           -> a === b
    uniques x y = ?uniques_rhs

    export
    unique : (fs : SnocList Fix)
          -> {a,b : Local rs fs}
          -> Local rs fs tm a
          -> Local rs fs tm b
          -> a === b
    unique {tm} fs x y with (x)
      unique {tm = End} fs x End | End = Refl
      unique {tm = (Call f)} fs x (Call y) | (Call idx) = ?unique_rhs_rhs_2
      unique {tm = (Rec f kast)} fs x (Rec y) | (Rec z) with (unique (fs :< MkFix f) z y)
        unique {tm = (Rec f kast)} fs x (Rec y) | (Rec z) | Refl = Refl

      unique {tm = (Comm cty r tms)} fs x (Comm y w) | (Comm idx z) = ?unique_rhs_rhs_4

-- [ EOF ]
