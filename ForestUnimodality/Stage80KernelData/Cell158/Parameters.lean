import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (21688053216056108919218559/100000000000000000000000000)
  B := (65307122708632356355984427/1000000000000000000000000000)
  C := (75190364596640956243445153/10000000000000000000000000000)
  dδ := (2397330144162358733783691/20000000000000000000000000)
  dM := (3988875954170369685092279/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(37071843717549457508653177/5000000000000000000000000), (12352226091179867140112947/500000000000000000000000), (34928610677711087184604821/5000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11953/22578)
  hi := (31883/60208)
  vmin := (903085975/3625003264)
  damping := (903085975/3625003264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell158
