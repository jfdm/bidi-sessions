module Sessions.Types.Global.Projection

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import  Extra

import Sessions.Types.Global
import Sessions.Types.Local
import Sessions.Types.Local.Merge.Projection

%default total

namespace Merge

  public export
  data Project : (how : (p : AtIndex r rs n) -> (g : Global rs fs) -> (l : Local rs fs) -> Type)
              -> (p : AtIndex r rs n)
              -> (xs : List (Global.Branch rs fs))
              -> (y  : List (Local rs fs))
                    -> Type

    where
      Last : Project how p Nil Nil
      Next : how p x y
          -> Project how p xs ys
          -> Project how p (B l t x::xs) (y::ys)


  export
  project : {0 how : (p : AtIndex r rs n) -> (g : Global rs fs) -> (l : Local rs fs) -> Type}
         -> (f : (p : AtIndex r rs n) -> (g : Global rs fs) -> Dec (DPair (Local rs fs) (how p g)))
         -> (whom : AtIndex r rs n)
         -> (xs : List (Global.Branch rs fs))
               -> Dec (DPair (List $ Local rs fs) (Project how whom xs))
  project f _ []
    = Yes ([] ** Last)
  project f whom (B l t x :: xs) with (f whom x)
    project f whom (B l t x :: xs) | (Yes (y ** py)) with (project f whom xs)
      project f whom (B l t x :: xs) | (Yes (y ** py)) | (Yes (ys ** pys))
        = Yes (y :: ys ** Next py pys)
      project f whom (B l t x :: xs) | (Yes (y ** py)) | (No no)
        = No $ \case ((y :: ys) ** (Next x xs)) => no (ys ** xs)
    project f whom (B l t x :: xs) | (No no)
      = No $ \case ((y :: ys) ** (Next x xs)) => no (y ** x)

namespace Branches

  public export
  data Project : (how : (p : AtIndex r rs n) -> (g : Global rs fs) -> (l : Local rs fs) -> Type)
              -> (p : AtIndex r rs n)
              -> (xs : List (Global.Branch rs fs))
              -> (ys : List (Local.Branch rs fs))
                    -> Type
    where
      Stop : Project how whom Nil Nil
      Next : how whom x y
          -> Branches.Project how whom xs ys
          -> Project how whom (B l t x::xs) (B l t y::ys)

  export
  project : {0 how : (p : AtIndex r rs n) -> (g : Global rs fs) -> (l : Local rs fs) -> Type}
         -> (f : (p : AtIndex r rs n) -> (g : Global rs fs) -> Dec (DPair (Local rs fs) (how p g)))
         -> (whom : AtIndex r rs n)
         -> (xs : List (Global.Branch rs fs))
               -> Dec (DPair (List (Local.Branch rs fs)) (Project how whom xs))
  project f whom []
    = Yes ([] ** Stop)
  project f whom ((B l t x) :: xs) with (f whom x)
    project f whom ((B l t x) :: xs) | (Yes (y ** py)) with (Branches.project f whom xs)
      project f whom ((B l t x) :: xs) | (Yes (y ** py)) | (Yes (ys ** pys))
        = Yes (B l t y :: ys ** Next py pys)
      project f whom ((B l t x) :: xs) | (Yes (y ** py)) | (No no)
        = No $ \case ((B l t y :: ys) ** (Next x xs)) => no (ys ** xs)
    project f whom ((B l t x) :: xs) | (No no)
      = No $ \case (((B l t y :: ys) ** (Next x xs))) => no (y ** x)

public export
data Project : (p : AtIndex r rs n)
            -> (g : Global rs fs)
            -> (l : Local rs fs)
                 -> Type
  where
    Stop : Project p Stop  Stop
    Call : Project p (Call idx) (Call idx)
    Rec : Project p x y
       -> Project p (Rec x) (Rec y)

    Select : (prf : whom = s)
          -> (bs  : Branches.Project Project whom xs ys)
                 -> Project whom
                            (Choice s r notSR xs)
                            (Comm SEND r ys )

    Offer : (prf : whom = r)
         -> (bs  : Branches.Project Project whom xs ys)
                -> Project whom
                           (Choice s r notSR xs)
                           (Comm RECV s ys)

    Merge : {ys : _}
         -> (prfS : EqualNot whom s)
         -> (prfR : EqualNot whom r)
         -> (prfM : Merge.Project Project whom xs ys)
         -> (prfF : Merges Projection.Merge ys y)
                 -> Project whom
                            (Choice s r notSR xs)
                            y


mutual
  namespace Branches
    export
    project' : (whom : AtIndex r rs n)
           -> (xs : List (Global.Branch rs fs))
                 -> Dec (DPair (List (Local.Branch rs fs)) (Project Project whom xs))
    project' = Branches.project project

    export
    unique : Branches.Project Project whom xs as
          -> Branches.Project Project whom xs bs
          -> as === bs
    unique Stop Stop = Refl
    unique (Next x xs) (Next y ys) with (unique x y)
      unique (Next x xs) (Next y ys) | Refl with (unique xs ys)
        unique (Next x xs) (Next y ys) | Refl | Refl = Refl

  namespace Merge

    export
    project' : (whom : AtIndex r rs n)
            -> (xs : List (Global.Branch rs fs))
                  -> Dec (DPair (List $ Local rs fs) (Project Project whom xs))
    project' = Merge.project project

    export
    unique : Merge.Project Project whom xs as
          -> Merge.Project Project whom xs bs
          -> as === bs
    unique Last Last = Refl
    unique (Next x xs) (Next y ys) with (unique x y)
      unique (Next x xs) (Next y ys) | Refl with (unique xs ys)
        unique (Next x xs) (Next y ys) | Refl | Refl = Refl

  mergeFails : (DPair (Local rs fs) (Merges Projection.Merge ys) -> Void) -> EqualNot whom r_1 -> EqualNot whom s_0
             -> Merge.Project Project whom xs ys
             -> DPair (Local rs fs) (Project whom (Choice s_0 r_1 notSR xs)) -> Void
  mergeFails f notR notS _ (Comm SEND _ _ ** Select prf bs) = toVoid prf notS
  mergeFails f notR notS _ (Comm RECV _ _ ** Offer prf bs) = toVoid prf notR
  mergeFails f notR notS p (fst ** (Merge prfS prfR prfM prfF)) with (unique p prfM)
    mergeFails f notR notS p (fst ** (Merge prfS prfR prfM prfF)) | Refl = f (fst ** prfF)

  export
  unique : Project whom g a
        -> Project whom g b
        -> a === b
  unique Stop Stop = Refl
  unique Call Call = Refl
  unique (Rec x) (Rec y) with (unique x y)
    unique (Rec x) (Rec y) | Refl = Refl
  unique (Select Refl as) (Select Refl bs) with (unique as bs)
    unique (Select Refl as) (Select Refl bs) | Refl = Refl

  unique (Select {notSR} Refl bs) (Offer Refl x)
    = void (toVoid Refl notSR)

  unique (Select Refl bs) (Merge prfS prfR prfM prfF)
     = void (toVoid Refl prfS)

  unique (Offer {notSR} Refl bs) (Select Refl x)
    = void (toVoid Refl notSR)

  unique (Offer Refl as) (Offer Refl bs) with (unique as bs)
    unique (Offer Refl as) (Offer Refl bs) | Refl = Refl

  unique (Offer Refl bs) (Merge prfS prfR prfM prfF)
    = void (toVoid Refl prfR)

  unique (Merge prfS prfR prfM prfF) (Select Refl bs)
    = void (toVoid Refl prfS)
  unique (Merge prfS prfR prfM prfF) (Offer Refl bs)
    = void (toVoid Refl prfR)

  unique (Merge _ _ apm apf) (Merge _ _ bpm bpf) with (unique apm bpm)
    unique (Merge _ _ apm apf) (Merge _ _ bpm bpf) | Refl with (unique apf bpf)
      unique (Merge _ _ apm apf) (Merge _ _ bpm bpf) | Refl | Refl = Refl

  export
  project : (whom : AtIndex r rs n)
         -> (g    : Global rs fs)
               -> Dec (DPair (Local rs fs)
                             (Project whom g))
  project whom Stop
    = Yes (Stop ** Stop)

  project whom (Call x)
    = Yes (Call x ** Call)

  project whom (Rec x) with (project whom x)
    project whom (Rec x) | (Yes (l ** prf))
      = Yes (Rec l ** Rec prf)
    project whom (Rec x) | (No no)
      = No $ \case ((Rec l) ** (Rec y)) => no (l ** y)

  project whom (Choice s r notSR xs) with (involved whom s r)
    project whom (Choice s r notSR xs) | (Sends prfS) with (Branches.project' whom xs)
      project whom (Choice whom r notSR xs) | (Sends Refl) | (Yes (fst ** snd))
        = Yes (Comm SEND r fst ** Select Refl snd)

      project whom (Choice whom r notSR xs) | (Sends Refl) | (No no)
        = No $ \case (Comm SEND _ _ ** Select prf bs) => no (_ ** bs)
                     (Comm RECV _ _ ** Offer prf bs) => no (_ ** bs)
                     (_ ** Merge ps pr pm pf) => toVoid Refl ps

    project r (Choice s r notSR xs) | (Recvs Refl) with (Branches.project' r xs)
      project r (Choice s r notSR xs) | (Recvs Refl) | (Yes ((fst ** snd)))
        = Yes (Comm RECV s fst ** Offer Refl snd)

      project r (Choice s r notSR xs) | (Recvs Refl) | (No no)
        = No $ \case (Comm SEND _ _ ** Select prf bs) => no (_ ** bs)
                     (Comm RECV _ _ ** Offer prf bs) => no (_ ** bs)
                     (_ ** Merge ps pr pm pf) => toVoid Refl pr


    project whom (Choice s r notSR xs) | (Skips prfSNot prfRNot) with (Merge.project' whom xs)
      project whom (Choice s r notSR xs) | (Skips prfSNot prfRNot) | (Yes (ys ** pYS)) with (Projection.merges ys)
        project whom (Choice s r notSR xs) | (Skips prfSNot prfRNot) | (Yes (ys ** pYS)) | (Yes (y ** prf))
          = Yes (y ** Merge prfSNot prfRNot pYS prf)
        project whom (Choice s r notSR xs) | (Skips prfSNot prfRNot) | (Yes (ys ** pYS)) | (No no)
          = No (mergeFails no prfRNot prfSNot pYS)

      project whom (Choice s r notSR xs) | (Skips prfSNot prfRNot) | (No no)
        = No $ \case (fst ** snd) => case snd of
                                          (Select prf bs) => toVoid prf prfSNot
                                          (Offer prf bs) => toVoid prf prfRNot
                                          (Merge prfS prfR prfM prfF)
                                            => no (_ ** prfM)

-- [ EOF ]
