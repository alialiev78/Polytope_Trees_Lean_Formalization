module

import Article
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  let requiredModules : Array Name := #[
    `Proofs.AllFacetsOrientedFlags,
    `Proofs.EuclideanFacetTransporters,
    `Proofs.EuclideanRegularPolytopeMass,
    `Proofs.EuclideanPolytopeRealization,
    `Proofs.IntrinsicGeometricPresentations]
  for mod in requiredModules do
    unless env.header.moduleNames.contains mod do
      throwError "Required all-facets module {mod} was not imported"
  let requiredEndpoints : Array Name := #[
    ``PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell.facet_isometry_extends_uniquely,
    ``PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell.orientedFlags,
    ``PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell.allFacetPalette,
    ``PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell.tau_eq_h_mul_r,
    ``PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell.polytopeAffineCompatible_iff_action,
    ``PolytopeCounting.FacetPairing.EuclideanGeometry.RegularCell.intrinsic_boundary_mass_formula]
  for name in requiredEndpoints do
    let _ ← getConstInfo name
  let mut checked : Nat := 0
  let mut geometryChecked : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx]!
      let isGeometric := mod ∈ #[`Proofs.AllFacetsOrientedFlags, `Proofs.ConcreteGeometricFlagInterface, `Proofs.EuclideanFacetTransporters, `Proofs.EuclideanPolytopeRealization, `Proofs.EuclideanRegularPolytopeMass, `Proofs.FacetOrientationCompatibility, `Proofs.GeometricFacetExtension, `Proofs.GeometricFlagTransport, `Proofs.IntrinsicFacetRestriction, `Proofs.IntrinsicGeometricPresentations, `Proofs.RegularPolytopeReflections, `Proofs.SupportingFaceFlags, `Proofs.PublicationGeometry]
      if isGeometric || mod.toString.startsWith "Proofs." || mod.toString == "Solution" then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Unexpected axiom {ax} in {name} (module {mod})"
        checked := checked + 1
        if isGeometric then geometryChecked := geometryChecked + 1
  if geometryChecked == 0 then
    throwError "The geometric modules were not imported; the audit is incomplete"
  logInfo m!"Axiom audit passed: {checked} project declarations, including {geometryChecked} geometric declarations; only propext, Quot.sound, Classical.choice."
