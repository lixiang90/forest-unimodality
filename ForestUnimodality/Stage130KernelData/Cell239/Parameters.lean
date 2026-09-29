import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell239
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 21
  A := (3744654583814374304751027/20000000000000000000000000)
  B := (707760130813727349717579/31250000000000000000000000)
  C := (1469679442519272955305909/31250000000000000000000000)
  dδ := (25569401840084188259893949/1000000000000000000000000000)
  dM := (181628284812117247667973/800000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(10708698236061389152951051/2000000000000000000000000), (2200368083949227893114653/1250000000000000000000000)]
  retention := ![(7/10), (3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2/3)
  hi := (35/52)
  vmin := (595/2704)
  damping := (1487500000000000000000000000000000000000000/16679631437841016065908406636280732186620121)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell239
