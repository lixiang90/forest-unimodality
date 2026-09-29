import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 89
  A := (-13527725190612238004206347/10000000000000000000000000)
  B := (17652112373182504700963591/200000000000000000000000000)
  C := (-70617913273318623414848139/100000000000000000000000000000)
  dδ := (62673814984240003300719479/1000000000000000000000000000)
  dM := (23522817646268130492223647/25000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5718635272181129103330477/500000000000000000000000), (89303741892222205933649093/10000000000000000000000000), (13443525022300556770460389/200000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49/99)
  hi := (131/264)
  vmin := (2450/9801)
  damping := (2450/9801)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell063
