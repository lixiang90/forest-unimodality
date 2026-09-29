import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 88
  A := (-2039460433333355944540699/1250000000000000000000000)
  B := (1250423517676117236840927/12500000000000000000000000)
  C := (7577710746917118087018217/2000000000000000000000000000)
  dδ := (3066795865674034476944243/50000000000000000000000000)
  dM := (10722262599012130895176353/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2986160818131364358407609/250000000000000000000000), (16937999096800948617413951/20000000000000000000000000), (18379837841006946064226213/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4657/8862)
  hi := (111/211)
  vmin := (11100/44521)
  damping := (11100/44521)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell128
