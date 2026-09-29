import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 92
  A := (-14095010094147869994429811/10000000000000000000000000)
  B := (88529914980594787143886037/1000000000000000000000000000)
  C := (50621427316298501803554233/100000000000000000000000000000)
  dδ := (61444729987717328079099843/1000000000000000000000000000)
  dM := (23037446286473732917111923/25000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12268352118807772654918153/1000000000000000000000000), (8296492030690423291616753/125000000000000000000000), (5944641055269755725021241/500000000000000000000000)]
  retention := ![(7/10), (1/100), (1/1000)]
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
end ForestUnimodality.Stage130KernelData.Cell071
