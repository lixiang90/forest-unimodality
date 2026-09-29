import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 62
  A := (-2585158120376469362255989/2500000000000000000000000)
  B := (48319931805441862504579831/500000000000000000000000000)
  C := (22376178379183612283595539/50000000000000000000000000000)
  dδ := (78481160511639405652495327/1000000000000000000000000000)
  dM := (13313134995065305232753161/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12203845482035786673691291/2500000000000000000000000), (429466068908353904021169/80000000000000000000000), (50638049060736619821909699/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (405/808)
  hi := (203/404)
  vmin := (40803/163216)
  damping := (40803/163216)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell063
