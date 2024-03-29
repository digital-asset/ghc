{-# LANGUAGE DamlSyntax #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Example where

{-
This file contains an example of a DAML template which can be compiled, desugared, and type-check:
$ ./_build/stage1/bin/ghc ./Example.hs

A minimal environment (to support the code generated by desugaring) is provided in:
  ./DA/Internal/Desugar.hs
  ./GHC/Types.hs
-}

import DA.Internal.Desugar
import GHC.Types


template HasAuthority
  with
    party: Party
  where
    signatory party


template ProposeConsortiumAuthority
  with
    proposer: Party
    accepted: [Party]
    obs: [Party]
    consortiumParty: Party
  where
    signatory proposer, accepted
    observer obs

    choice Accept : ContractId ProposeConsortiumAuthority
      with
        who: Party
      where
        controller who
      do
        create this with accepted = who :: accepted

    choice Ratify : ContractId HasAuthority
      where
        controller proposer
      do
        exercise self Ratify1

    choice Ratify1 : ContractId HasAuthority
      where
        controller proposer
        authority accepted -- restrict authority
      do
        exercise self Ratify2

    choice Ratify2 : ContractId HasAuthority
      where
        controller accepted
        authority consortiumParty -- gain authority
      do
        create HasAuthority with party = consortiumParty




_CONTROLLER : [Party]
_CONTROLLER = undefined
_OBSERVER : [Party]
_OBSERVER = undefined
_AUTHORITY : [Party]
_AUTHORITY = undefined

_BODY : Update ()
_BODY = undefined

template TrySyntax
  with
    p: Party
  where
    signatory p

    choice X_old_just_controller : ()
      controller _CONTROLLER
      do _BODY

    choice X_old_observer_and_controller : ()
      observer _OBSERVER
      controller _CONTROLLER
      do _BODY

    choice X_new_just_controllerX : () where { controller _CONTROLLER } do _BODY

    choice X_new_just_controller : ()
      where
        controller _CONTROLLER
      do _BODY

    choice X_new_observer_and_controllerX : () where { observer _OBSERVER; controller _CONTROLLER } do _BODY

    choice X_new_observer_and_controller : ()
      where
        observer _OBSERVER
        controller _CONTROLLER
      do _BODY

    choice X_new_controller_and_observer : ()
      where
        controller _CONTROLLER
        observer _OBSERVER
      do _BODY

    choice X_new_authority_and_controller : ()
      where
        authority _AUTHORITY
        controller _CONTROLLER
      do _BODY

    choice X_new_observer_authority_and_controllerX : ()
      where { observer _OBSERVER; authority _AUTHORITY; controller _CONTROLLER } do _BODY

    choice X_new_observer_authority_and_controller : ()
      where
        observer _OBSERVER
        authority _AUTHORITY
        controller _CONTROLLER
      do _BODY

    choice X_new_authority_observer_and_controller : () -- switch the order of A/O
      where
        authority _AUTHORITY
        observer _OBSERVER
        controller _CONTROLLER
      do _BODY

    choice X_new_controller_authority_observer : () -- controller first
      where
        controller _CONTROLLER
        authority _AUTHORITY
        observer _OBSERVER
      do _BODY

    choice X_new_authority_controller_observer : () -- controller in middle
      where
        authority _AUTHORITY
        controller _CONTROLLER
        observer _OBSERVER
      do _BODY
