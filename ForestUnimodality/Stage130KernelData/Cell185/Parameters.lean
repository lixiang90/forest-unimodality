import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell185
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-3207932479946056549806599/2000000000000000000000000)
  B := (11153706386504039227425267/100000000000000000000000000)
  C := (12192718177473865857202151/2500000000000000000000000000)
  dδ := (17628823152933625895144587/250000000000000000000000000)
  dM := (1670694888707011322229179/1250000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(36531596323019019934008611/5000000000000000000000000), (7331252160930851191622537/1250000000000000000000000), (30579542280668871256921193/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7977/15052)
  hi := (95749/180624)
  vmin := (8126696375/32625029376)
  damping := (8126696375/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell185
