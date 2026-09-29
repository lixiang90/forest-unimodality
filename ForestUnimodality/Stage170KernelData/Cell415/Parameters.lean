import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell415
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (39)
  A := (6461896821441414644482393 / 500000000000000000000000000)
  B := (13586640629213636577432567 / 500000000000000000000000000)
  C := (4704372787528497343312317 / 62500000000000000000000000)
  dδ := (12275751992576655960420773 / 500000000000000000000000000)
  dM := (22682757635035668370912521 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(15282570453136090193879681 / 1000000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (123 / 203)
  hi := (63 / 103)
  vmin := (2520 / 10609)
  damping := (2520 / 10609)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell415
