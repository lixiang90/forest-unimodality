import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 34
  A := (16965800471560672829696159/5000000000000000000000000)
  B := (-40811873566475212471438283/500000000000000000000000000)
  C := (-19680115793699031606633909/5000000000000000000000000000)
  dδ := (2915236185078596276021301/20000000000000000000000000)
  dM := 0
  wL := 0
  wR := 0
  wC := 1
  price := ![(75637685081927035213311683/10000000000000000000000000), (3058082536295120057445729/250000000000000000000000), (3491049130968428215737731/200000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9237/19012)
  hi := (4631/9506)
  vmin := (90291675/361456144)
  damping := (90291675/361456144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell051
