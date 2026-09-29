import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 19
  A := (13784271483215234934682769/250000000000000000000000000)
  B := (30524998788583564135468151/1000000000000000000000000000)
  C := (-5877528595109265605045401/125000000000000000000000000)
  dδ := (6888377433008015075788233/250000000000000000000000000)
  dM := (32683219663527104470804319/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(15813244158609146561289549/100000000000000000000000000), (58541869376268174107735831/10000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13/42)
  hi := (20/63)
  vmin := (377/1764)
  damping := (3770000000000000000000000000000000000000000/43524955408804071509263948678105342569819369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell008
