import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 84
  A := (-12443922555269097307473203/10000000000000000000000000)
  B := (88021065660953273779298911/1000000000000000000000000000)
  C := (96973274173735247907085499/100000000000000000000000000000)
  dδ := (4121430309385221146811773/62500000000000000000000000)
  dM := (98402926152844037710476499/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(11658682461304806565749459/1000000000000000000000000), (71031962130959854562206601/1000000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (51/101)
  hi := (10429/20604)
  vmin := (106115075/424524816)
  damping := (106115075/424524816)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell075
