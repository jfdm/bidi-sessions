module Sessions.Elab

import Sessions.Types.Local
import Sessions.Types.Local.Subset

import Sessions.Types.Global
import Sessions.Types.Global.Projection

import Sessions.AST

import public Sessions.Elab.Expr
import public Sessions.Elab.Local
import public Sessions.Elab.Global

import public Sessions.Elab.Terms

%default total

namespace Session
  public export
  data Check : (rs : SnocList Role)
            -> (tm : Session.AST)
                  -> Type
    where
      Session : {tyProj,tyG,tySyn,p : _}
             -> Global rs Lin tmty tyG
             -> (whom : AtIndex p rs n)
             -> Project whom tyG tyProj
             -> Synth rs Lin Lin tm tySyn
             -> Subset tySyn tyProj
             -> Check rs (Session tmty n tm)

  projectFails : (widx : AtIndex w rs whom)
              -> Global rs Lin g gty
              -> (DPair (Local rs [<]) (Project widx gty) -> Void)
              -> Check rs (Session g whom tm) -> Void
  projectFails widx gty f (Session gtm whom p _ _) with (unique widx whom)
    projectFails widx gty f (Session gtm whom p _ _) | Refl with (unique2 widx whom)
      projectFails widx gty f (Session gtm widx p _ _) | Refl | Refl with (unique gty gtm)
        projectFails widx gty f (Session gtm widx p _ _) | Refl | Refl | Refl = f (_ ** p)

  subsetFails : (Subset tySyn tyProj -> Void)
             -> (widx : AtIndex w rs whom )
             -> Project widx gty tyProj
             -> Global rs [<] g gty
             -> Synth rs [<] [<] tm tySyn
             -> Check rs (Session g whom tm) -> Void
  subsetFails f pidx pGiv gGiv tmG (Session gExp y pExp tmExp prf) with (unique gGiv gExp)
    subsetFails f pidx pGiv gGiv tmG (Session gExp y pExp tmExp prf) | Refl with (unique tmG tmExp)
      subsetFails f pidx pGiv gGiv tmG (Session gExp y pExp tmExp prf) | Refl | Refl with (unique pidx y)
        subsetFails f pidx pGiv gGiv tmG (Session gExp y pExp tmExp prf) | Refl | Refl | Refl with (unique2 pidx y)
          subsetFails f pidx pGiv gGiv tmG (Session gExp pidx pExp tmExp prf) | Refl | Refl | Refl | Refl with (unique pGiv pExp)
            subsetFails f pidx pGiv gGiv tmG (Session gExp pidx pExp tmExp prf) | Refl | Refl | Refl | Refl | Refl = f prf

  export
  check : (rs : SnocList Role)
       -> (tm : Session.AST)
             -> Dec (Check rs tm)
  check rs (Session g whom tm) with (synth rs Lin g)
    check rs (Session g whom tm) | (Yes (gty ** gtm)) with (index rs whom)
      check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes (w ** widx)) with (project widx gty)
        check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes (w ** widx)) | (Yes (tyProj ** prfP)) with (synth rs Lin Lin tm)
          check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes (w ** widx)) | (Yes (tyProj ** prfP)) | (Yes (tySyn ** prfS)) with (subset tySyn tyProj)
            check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes (w ** widx)) | (Yes (tyProj ** prfP)) | (Yes (tySyn ** prfS)) | (Yes prf)
              = Yes (Session gtm widx prfP prfS prf)
            check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes (w ** widx)) | (Yes (tyProj ** prfP)) | (Yes (tySyn ** prfS)) | (No no)
              = No (subsetFails no widx prfP gtm prfS)
          check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes (w ** widx)) | (Yes (tyProj ** prfP)) | (No no)
            = No $ \case (Session g whom prfP prfTm _) => no (_ ** prfTm)

        check rs (Session g whom tm) | (Yes (gty ** gtm)) | (Yes (w ** widx)) | (No no)
          = No (projectFails widx gtm no)
      check rs (Session g whom tm) | (Yes (gty ** gtm)) | (No no)
        = No $ \case (Session _ whom _ _ _) => no (_ ** whom)
    check rs (Session g whom tm) | (No no)
      = No $ \case (Session gty _ _ _ _) => no (_ ** gty)

-- [ EOF ]
