import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell384
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (114)
  A := (-9224510932364293430651969 / 5000000000000000000000000)
  B := (2313072700927251354463543 / 25000000000000000000000000)
  C := (-10751789282958614966598243 / 100000000000000000000000000000)
  dδ := (26857631839321608607784597 / 500000000000000000000000000)
  dM := (16737533381408565072434591 / 20000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(3038637133238658805112209 / 250000000000000000000000), (19989390306957335496917949 / 200000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49 / 99)
  hi := (1 / 2)
  vmin := (2450 / 9801)
  damping := (2450 / 9801)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell384
