import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 72
  A := (-3886880624679548514848193/2000000000000000000000000)
  B := (3276841158313844454275099/25000000000000000000000000)
  C := (54894911570438804926386211/10000000000000000000000000000)
  dδ := (18112831545618931355923209/250000000000000000000000000)
  dM := (8076328432362135699776329/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(16553991299564213335315799/1000000000000000000000000), (53435616553070573786499153/1000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (94453/178928)
  hi := (47239/89464)
  vmin := (1994666775/8003807296)
  damping := (1994666775/8003807296)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell140
