import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell131.Parameters
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch000_049
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch050_099
import ForestUnimodality.BinomialMassData.Q47239_89464.Batch100_149
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch000_049
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch050_099
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree000.table
  base := (2883458283051364997639609531/50000000000000000000000000)
  polynomial :=
    { denominator := 223660000000000000000000000000000000000000000
      center := (1464409)
      previous := (0)
      next := (1308975)
      square := (33850383135862496497003882153600000000000000)
      linear := (-157616261718777656546386367089400000000000000)
      constant := (12898285591745365907441501354069200000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree000.table
  base := (2883458283051364997639609531/50000000000000000000000000)
  polynomial :=
    { denominator := 447320000000000000000000000000000000000000000
      center := (2929593)
      previous := (0)
      next := (2617175)
      square := (67700766271724992994007764307200000000000000)
      linear := (-315232523437555313092772734178800000000000000)
      constant := (25796571183490731814883002708138400000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree001.table
  base := (173570535622458420098503137769691718382171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-2162387217039842651163730340424237800000000000000)
      constant := (87862816615765762652696343874374117328624847882476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree001.table
  base := (347080576370507693784959749582601938060953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-4324985998974284442930566955111935600000000000000)
      constant := (175695975675819394574140347161045262157249732132068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12480156559969647623/25000000000000000000)
  directionHi := (49920626239878590493/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree002.table
  base := (109112189706607176858115516956683849519573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-2562151779278594769169221937687715400000000000000)
      constant := (56865636723331978967562784123069361271882779512788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree002.table
  base := (218156637071070752055650911634256799250061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-5124726688346387819544656423902350800000000000000)
      constant := (113698818160702757132063536523485310785952847515316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12480156559969647623/25000000000000000000)
  centralHi := (49920626239878590493/100000000000000000000)
  directionLo := (7059842667059450639/10000000000000000000)
  directionHi := (70598426670594506391/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree003.table
  base := (72111478219250636090290986886743409952081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-2961916341517346887174713534951193000000000000000)
      constant := (39814892415494228749997275721139402315899057386436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree003.table
  base := (28832982266427594306511321945168550957613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-5924467377718491196158745892692766000000000000000)
      constant := (79603231650215246707883549154911663382590848795140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7059842667059450639/10000000000000000000)
  centralHi := (70598426670594506391/100000000000000000000)
  directionLo := (8646506099312579899/10000000000000000000)
  directionHi := (86465060993125798991/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree004.table
  base := (100397355083324067587726483148399850386029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-3361680903756099005180205132214670600000000000000)
      constant := (30522778432935712253562004146241877013906478958362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree004.table
  base := (100351863432201993274414635851104204529193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-6724208067090594572772835361483181200000000000000)
      constant := (61026558031257036825865054062228183316689448649508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8646506099312579899/10000000000000000000)
  centralHi := (86465060993125798991/100000000000000000000)
  directionLo := (12480156559969647623/12500000000000000000)
  directionHi := (19968250495951436197/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree005.table
  base := (73328151262198809523032792300132366863759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-3761445465994851123185696729478148200000000000000)
      constant := (25632842138046604167526154905183294739684466318302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree005.table
  base := (732934085655483552256104866311328240087/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-7523948756462697949386924830273596400000000000000)
      constant := (51253560559446867867667893751214676846619814217200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12480156559969647623/12500000000000000000)
  centralHi := (19968250495951436197/20000000000000000000)
  directionLo := (69766196094830157/62500000000000000)
  directionHi := (111625913751728251201/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree006.table
  base := (55710991530293042869590494160054519628117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-4161210028233603241191188326741625800000000000000)
      constant := (23318126112254631436817226464393981623665564104426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree006.table
  base := (2227370016253572722125880044004669422887/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-8323689445834801326001014299064011600000000000000)
      constant := (46629852732773359121692765066530424414017312474300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69766196094830157/62500000000000000)
  centralHi := (111625913751728251201/100000000000000000000)
  directionLo := (24456012385579075971/20000000000000000000)
  directionHi := (7642503870493461241/6250000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree007.table
  base := (8709934638073218589401825620005567516899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-4560974590472355359196679924005103400000000000000)
      constant := (22579104221045113090345480170614705233183878046110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree007.table
  base := (21764258097463697312691117754897033503291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-9123430135206904702615103767854426800000000000000)
      constant := (45156547329514372344670799143677928510299618226392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24456012385579075971/20000000000000000000)
  centralHi := (7642503870493461241/6250000000000000000)
  directionLo := (66038781161662092001/50000000000000000000)
  directionHi := (132077562323324184003/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree008.table
  base := (17320575143212003428343290983372863704181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-4960739152711107477202171521268581000000000000000)
      constant := (22864752861417808654932418103419041125246092094036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree008.table
  base := (34623783931614464473747078604871064304221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-9923170824579008079229193236644842000000000000000)
      constant := (45731909270291487136363221523572447451088075212276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66038781161662092001/50000000000000000000)
  centralHi := (132077562323324184003/100000000000000000000)
  directionLo := (141196853341189012781/100000000000000000000)
  directionHi := (70598426670594506391/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree009.table
  base := (13878502926942020693132789000772835495611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-5360503714949859595207663118532058600000000000000)
      constant := (23867821637633420201866800978948189623648693611116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree009.table
  base := (6935552247907711898530628391311700663391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-10722911513951111455843282705435257200000000000000)
      constant := (47741724069724331800735463651397074894954231475184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141196853341189012781/100000000000000000000)
  centralHi := (70598426670594506391/50000000000000000000)
  directionLo := (37440469679908942869/25000000000000000000)
  directionHi := (149761878719635771477/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree010.table
  base := (1110033085991888064162060783065099300441/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-5760268277188611713213154715795536200000000000000)
      constant := (25414083128986982618212931133363910139896357385960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree010.table
  base := (5546911333507881093743982156742434284837/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-11522652203323214832457372174225672400000000000000)
      constant := (50837753055213077418934537791011135530444730692688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37440469679908942869/25000000000000000000)
  centralHi := (149761878719635771477/100000000000000000000)
  directionLo := (39465720284995867381/25000000000000000000)
  directionHi := (6314515245599338781/4000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree011.table
  base := (4391864406988285454238410744482816842223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-6160032839427363831218646313059013800000000000000)
      constant := (27402324125727511849667441126777892773552016032376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree011.table
  base := (17555729363454769312720746701655690823559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-12322392892695318209071461643016087600000000000000)
      constant := (54817718208333163344413223950684897343345110805404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39465720284995867381/25000000000000000000)
  centralHi := (6314515245599338781/4000000000000000000)
  directionLo := (165567986537247602849/100000000000000000000)
  directionHi := (3311359730744952057/2000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree012.table
  base := (13614364426639097285868965407517743499419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-6559797401666115949224137910322491400000000000000)
      constant := (29771758424834838466652260223506148620940823873782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree012.table
  base := (850226490923651111880862623390733589773/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-13122133582067421585685551111806502800000000000000)
      constant := (59560143131948766098736273749007210464617408383808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165567986537247602849/100000000000000000000)
  centralHi := (3311359730744952057/2000000000000000000)
  directionLo := (8646506099312579899/5000000000000000000)
  directionHi := (172930121986251597981/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree013.table
  base := (5094505217203432940101800591899356538801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-6959561963904868067229629507585969000000000000000)
      constant := (32484274977058851846818888550991615947685046930756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree013.table
  base := (10179075993675238131259767209633152402263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-13921874271439524962299640580596918000000000000000)
      constant := (64988865189425583793245368497288151267544532894428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8646506099312579899/5000000000000000000)
  centralHi := (172930121986251597981/100000000000000000000)
  directionLo := (1439931020889242751/800000000000000000)
  directionHi := (44997844402788835969/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree014.table
  base := (7190841342345693849425418451506381516229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-7359326526143620185235121104849446600000000000000)
      constant := (35514723241421297968874562333433470055317287893962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree014.table
  base := (3590801211551289790858506393839230979091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-14721614960811628338913730049387333200000000000000)
      constant := (71053618791624582609686755195689097245184721155992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1439931020889242751/800000000000000000)
  centralHi := (44997844402788835969/25000000000000000000)
  directionLo := (186785879922822774499/100000000000000000000)
  directionHi := (373571759845645549/200000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree015.table
  base := (4549720835388774165281878936084321294409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-7759091088382372303240612702112924200000000000000)
      constant := (38845560794476981057189539571693773888981216194002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree015.table
  base := (567638462738122236745837398846930918873/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-15521355650183731715527819518177748400000000000000)
      constant := (77719339538337234834660536251547686087841850748704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186785879922822774499/100000000000000000000)
  centralHi := (373571759845645549/200000000000000000)
  directionLo := (96670877029647381419/50000000000000000000)
  directionHi := (193341754059294762839/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree016.table
  base := (442804288503384979710754232357348177733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-8158855650621124421246104299376401800000000000000)
      constant := (42463874625937858709231442753493118285023701584370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree016.table
  base := (275748377448966621330940202655552543163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-16321096339555835092141908986968163600000000000000)
      constant := (84960212744643905294453691559379637009939687158624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96670877029647381419/50000000000000000000)
  centralHi := (193341754059294762839/100000000000000000000)
  directionLo := (12480156559969647623/6250000000000000000)
  directionHi := (199682504959514361969/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree017.table
  base := (143898296186496418977725987696073421293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-8558620212859876539251595896639879400000000000000)
      constant := (46359698778255367909088720118468463433746768598554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree017.table
  base := (8525469451130075424293194977278725563/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-17120837028927938468755998455758578800000000000000)
      constant := (92756312499603001390412442210402854717886721107648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12480156559969647623/6250000000000000000)
  centralHi := (199682504959514361969/100000000000000000000)
  directionLo := (8233120595360000689/4000000000000000000)
  directionHi := (102914007442000008613/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree018.table
  base := (-338518281591335012467030984528490227291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-8958384775098628657257087493903357000000000000000)
      constant := (50525043749849991259839872659159842112334936857010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree018.table
  base := (-849783815268978252918313741270625625963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-17920577718300041845370087924548994000000000000000)
      constant := (101091662799998610459562693395581577138054096696744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8233120595360000689/4000000000000000000)
  centralHi := (102914007442000008613/50000000000000000000)
  directionLo := (211795280011783519171/100000000000000000000)
  directionHi := (52948820002945879793/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree019.table
  base := (-3321794130355713134353585386596044941627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-9358149337337380775262579091166834600000000000000)
      constant := (54953319790961777262284353601592888565358185102794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree019.table
  base := (-832070523305534869670527697971282482803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-18720318407672145221984177393339409200000000000000)
      constant := (109953085533419339207474890540546996166416088517328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211795280011783519171/100000000000000000000)
  centralHi := (52948820002945879793/25000000000000000000)
  directionLo := (217598964977895614863/100000000000000000000)
  directionHi := (13599935311118475929/6250000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree020.table
  base := (-4765883990995898002622115109743022543289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-9757913899576132893268070688430312200000000000000)
      constant := (59638980733361958256367730239938153858841594561358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree020.table
  base := (-4771908833873251855408924406729379400391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-19520059097044248598598266862129824400000000000000)
      constant := (119329488945157630441398761809810893103599900559204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217598964977895614863/100000000000000000000)
  centralHi := (13599935311118475929/6250000000000000000)
  directionLo := (69766196094830157/31250000000000000)
  directionHi := (223251827503456502401/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree021.table
  base := (-75547308523872442029638283084039730019/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-10157678461814885011273562285693789800000000000000)
      constant := (64577293402539362167681135822694695444300143953440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree021.table
  base := (-378085692909238202851769844111057876937/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-20319799786416351975212356330920239600000000000000)
      constant := (129211406915288142203824369959612237330293369267648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69766196094830157/31250000000000000)
  centralHi := (223251827503456502401/100000000000000000000)
  directionLo := (114382524241921187007/50000000000000000000)
  directionHi := (45753009696768474803/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree022.table
  base := (-224118703963816120050949194361170795661/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-10557443024053637129279053882957267400000000000000)
      constant := (69764180277939936841035982047415671476586363057344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree022.table
  base := (-7176970937587951296199801871883058311341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-21119540475788455351826445799710654800000000000000)
      constant := (139590684521460550042567886996537583489305966541004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114382524241921187007/50000000000000000000)
  centralHi := (45753009696768474803/20000000000000000000)
  directionLo := (234148492055781574119/100000000000000000000)
  directionHi := (5853712301394539353/2500000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree023.table
  base := (-2041014771970215043791566486763308020703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-10957207586292389247284545480220745000000000000000)
      constant := (75196106287458731986589293869537861404850251193864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree023.table
  base := (-8168841691081300460580665888384725844217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-21919281165160558728440535268501070000000000000000)
      constant := (150460251748526532255184397846403911452068513499548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234148492055781574119/100000000000000000000)
  centralHi := (5853712301394539353/2500000000000000000)
  directionLo := (935198878846569763/390625000000000000)
  directionHi := (239410912984721859329/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree024.table
  base := (-9032872957243071290902978863185710300831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-11356972148531141365290037077484222600000000000000)
      constant := (80869993318827758073026532460217716915352077729282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree024.table
  base := (-2259322389002443500290444269913182296797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-22719021854532662105054624737291485200000000000000)
      constant := (161813952563658866709850291265753191761579533492272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (935198878846569763/390625000000000000)
  centralHi := (239410912984721859329/100000000000000000000)
  directionLo := (24456012385579075971/10000000000000000000)
  directionHi := (244560123855790759711/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree025.table
  base := (-9788988475918123384438414146871233216547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-11756736710769893483295528674747700200000000000000)
      constant := (86783153007983557317685178677639689625277611671034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree025.table
  base := (-4896531166940755779866657884885423946291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-23518762543904765481668714206081900400000000000000)
      constant := (173646410508599627914793875268394336961827872757608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24456012385579075971/10000000000000000000)
  centralHi := (244560123855790759711/100000000000000000000)
  directionLo := (12480156559969647623/5000000000000000000)
  directionHi := (249603131199392952461/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree026.table
  base := (-10441813675321223054161889813358640816899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-12156501273008645601301020272011177800000000000000)
      constant := (92933232227723566352517239853712751261408136990778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree026.table
  base := (-10445567366680989403497064491098503802317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-24318503233276868858282803674872315600000000000000)
      constant := (185952919673823108478379620320783366013270715855948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12480156559969647623/5000000000000000000)
  centralHi := (249603131199392952461/100000000000000000000)
  directionLo := (25454624732791294161/10000000000000000000)
  directionHi := (254546247327912941611/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree027.table
  base := (-10999597092187567230195155258350971341261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-12556265835247397719306511869274655400000000000000)
      constant := (99318167862469582264731926614011540307816509448742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree027.table
  base := (-11003052374921332356688166972553500338271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-25118243922648972234896893143662730800000000000000)
      constant := (198729354236478163567359278860600218840138006385924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25454624732791294161/10000000000000000000)
  centralHi := (254546247327912941611/100000000000000000000)
  directionLo := (259395182979377396971/100000000000000000000)
  directionHi := (64848795744844349243/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree028.table
  base := (-1433697523731231643117926715600614147491/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-12956030397486149837312003466538133000000000000000)
      constant := (105936148684813606348576621041525444166057678526416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree028.table
  base := (-11472757907811303478072821123135794243549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-25917984612021075611510982612453146000000000000000)
      constant := (211972092199028284131927340163955283077170482054156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259395182979377396971/100000000000000000000)
  centralHi := (64848795744844349243/25000000000000000000)
  directionLo := (66038781161662092001/25000000000000000000)
  directionHi := (52831024929329673601/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree029.table
  base := (-11858127259249119277507837209307866568941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-13355794959724901955317495063801610600000000000000)
      constant := (112785582864809771401399863637865802801416110537702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree029.table
  base := (-474441890925157957059441222121611587387/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-26717725301393178988125072081243561200000000000000)
      constant := (225677950393397181459914530683632039102490293475700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66038781161662092001/25000000000000000000)
  centralHi := (52831024929329673601/20000000000000000000)
  directionLo := (134415399788554725471/50000000000000000000)
  directionHi := (268830799577109450943/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree030.table
  base := (-608541847922374947883671227434814820051/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-13755559521963654073322986661065088200000000000000)
      constant := (119865070071825405174256093534231890861791799442440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree030.table
  base := (-2434703620569138855567181921524090599587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-27517465990765282364739161550033976400000000000000)
      constant := (239844128671609029370822452455696590818518923379140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134415399788554725471/50000000000000000000)
  centralHi := (268830799577109450943/100000000000000000000)
  directionLo := (8544579086364314279/3125000000000000000)
  directionHi := (273426530763658056929/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree031.table
  base := (-12412638580643271753243124921013802456829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-14155324084202406191328478258328565800000000000000)
      constant := (127173377396083491630288155376825503130604041399238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree031.table
  base := (-6207549321720934370931573177511718921713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-28317206680137385741353251018824391600000000000000)
      constant := (254468161737717843786563328390905417371111529722744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8544579086364314279/3125000000000000000)
  centralHi := (273426530763658056929/100000000000000000000)
  directionLo := (277946283748553293493/100000000000000000000)
  directionHi := (138973141874276646747/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree032.table
  base := (-629393772146434514043018428706408210207/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-14555088646441158309333969855592043400000000000000)
      constant := (134709418491551786613303368601635663928244319831080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree032.table
  base := (-2518026232594421866562277536233780664379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-29116947369509489117967340487614806800000000000000)
      constant := (269547877424427568990809973685060303311493635153380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277946283748553293493/100000000000000000000)
  centralHi := (138973141874276646747/50000000000000000000)
  directionLo := (141196853341189012781/50000000000000000000)
  directionHi := (282393706682378025563/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree033.table
  base := (-12700377308954914773612368593329251632097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-14954853208679910427339461452855521000000000000000)
      constant := (142472235461659880377287717686901444139275066363134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree033.table
  base := (-1587805548536797576367734622222635241047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-29916688058881592494581429956405222000000000000000)
      constant := (285081360457240694489616865117866611260680651360544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141196853341189012781/50000000000000000000)
  centralHi := (282393706682378025563/100000000000000000000)
  directionLo := (286772164789392714151/100000000000000000000)
  directionHi := (35846520598674089269/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree034.table
  base := (-12753523412937883572575609596746024748327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-15354617770918662545344953050118998600000000000000)
      constant := (150460983095799259793060136880103708014385743550194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree034.table
  base := (-12755416540330695290946104344984308940771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-30716428748253695871195519425195637200000000000000)
      constant := (301066920921828276207180720511043908393396189895924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286772164789392714151/100000000000000000000)
  centralHi := (35846520598674089269/12500000000000000000)
  directionLo := (291084770165284094427/100000000000000000000)
  directionHi := (72771192541321023607/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree035.table
  base := (-12750297391503626304080098056196112701163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-15754382333157414663350444647382476200000000000000)
      constant := (158674915129826298962285243071778044348612291028586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree035.table
  base := (-12752030274345326182736343334471960936613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-31516169437625799247809608893986052400000000000000)
      constant := (317503066780817461673244647603780239671756867316972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291084770165284094427/100000000000000000000)
  centralHi := (72771192541321023607/25000000000000000000)
  directionLo := (295334407657417932813/100000000000000000000)
  directionHi := (147667203828708966407/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree036.table
  base := (-12693335225506027137743247006148397861031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-16154146895396166781355936244645953800000000000000)
      constant := (167113372254903796809127950262739217510661540253682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree036.table
  base := (-79343253924044084753119308896544412269/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-32315910126997902624423698362776467600000000000000)
      constant := (334388479888430875311396474335756297738933458853760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295334407657417932813/100000000000000000000)
  centralHi := (147667203828708966407/50000000000000000000)
  directionLo := (37440469679908942869/12500000000000000000)
  directionHi := (299523757439271542953/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree037.table
  base := (-6292483564628918370443388365416409052643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-16553911457634918899361427841909431400000000000000)
      constant := (175775771640209327164308931778293765921645969282292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree037.table
  base := (-2517283382797086283187573317511670614083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-33115650816370006001037787831566882800000000000000)
      constant := (351721995033819700310514788915396628629329276328260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37440469679908942869/12500000000000000000)
  centralHi := (299523757439271542953/100000000000000000000)
  directionLo := (151827657390477797813/50000000000000000000)
  directionHi := (303655314780955595627/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree038.table
  base := (-3106813547273979209107835248084326012209/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-16953676019873671017366919439172909000000000000000)
      constant := (184661597768934744409963954524376401230029877590392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree038.table
  base := (-2485715872547169177951381373325264130569/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-33915391505742109377651877300357298000000000000000)
      constant := (369502581611752159577262977906551655590820231615180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151827657390477797813/50000000000000000000)
  centralHi := (303655314780955595627/100000000000000000000)
  directionLo := (307731407430088105217/100000000000000000000)
  directionHi := (153865703715044052609/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree039.table
  base := (-12222020440030283054693104872423410168453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-17353440582112423135372411036436386600000000000000)
      constant := (193770394415307507216874313473857636990391727798966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree039.table
  base := (-12223231198940416290779994529929628967149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-34715132195114212754265966769147713200000000000000)
      constant := (387729327575959902925886898702172488031634993092556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307731407430088105217/100000000000000000000)
  centralHi := (153865703715044052609/50000000000000000000)
  directionLo := (62350842189367270663/20000000000000000000)
  directionHi := (77938552736709088329/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree040.table
  base := (-11970880973747085124009602945772537629333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-17753205144351175253377902633699864200000000000000)
      constant := (203101757614245699518233246839878496467684687218326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree040.table
  base := (-598599337537000960871627401797665949173/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-35514872884486316130880056237938128400000000000000)
      constant := (406401425378233424966741987154141898200297971792240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62350842189367270663/20000000000000000000)
  centralHi := (77938552736709088329/25000000000000000000)
  directionLo := (315725762279966939049/100000000000000000000)
  directionHi := (6314515245599338781/2000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree041.table
  base := (-2335053318022513447418705130241596420013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-18152969706589927371383394230963341800000000000000)
      constant := (212655329495549053779861021442250125426689448466430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree041.table
  base := (-5838138050381618160955069200638857198481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-36314613573858419507494145706728543600000000000000)
      constant := (425518159636961692906954827904872902861711956510328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315725762279966939049/100000000000000000000)
  centralHi := (6314515245599338781/2000000000000000000)
  directionLo := (159823985912196428107/50000000000000000000)
  directionHi := (63929594364878571243/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree042.table
  base := (-1133644543506089729129662576055822338841/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-18552734268828679489388885828226819400000000000000)
      constant := (222430792871852561071991607971174117306595193755020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree042.table
  base := (-5668683361566965879111618085772384895131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-37114354263230522884108235175518958800000000000000)
      constant := (445078896313479702051301553966015365947628788415528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159823985912196428107/50000000000000000000)
  centralHi := (63929594364878571243/20000000000000000000)
  directionLo := (323522634162788530129/100000000000000000000)
  directionHi := (32352263416278853013/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree043.table
  base := (-1095554200840360090700899407637981132391/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-18952498831067431607394377425490297000000000000000)
      constant := (232427866484412601413832220953787828076830803836020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree043.table
  base := (-2739095622495061606463164814184114757803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-37914094952602626260722324644309374000000000000000)
      constant := (465083073204291265826145879525071712853548768917328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323522634162788530129/100000000000000000000)
  centralHi := (32352263416278853013/10000000000000000000)
  directionLo := (65470287532532239213/20000000000000000000)
  directionHi := (163675718831330598033/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree044.table
  base := (-10533553874121451758323777394015553966877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-19352263393306183725399869022753774600000000000000)
      constant := (242646300823545814082369377436836139425700878908294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree044.table
  base := (-2633580095030678954571323976506220883263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-38713835641974729637336414113099789200000000000000)
      constant := (485530191582749024265400472291475672876288009078288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65470287532532239213/20000000000000000000)
  centralHi := (163675718831330598033/50000000000000000000)
  directionLo := (331135973074495205699/100000000000000000000)
  directionHi := (3311359730744952057/1000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree045.table
  base := (-10071366361824960959745422939763744739547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-19752027955544935843405360620017252200000000000000)
      constant := (253085874451514824899585584103622387479291628177034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree045.table
  base := (-10072065178721168336993999725137500572151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-39513576331346833013950503581890204400000000000000)
      constant := (506419808845733125676201804588010912894838353236644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331135973074495205699/100000000000000000000)
  centralHi := (3311359730744952057/1000000000000000000)
  directionLo := (334877741255184753601/100000000000000000000)
  directionHi := (167438870627592376801/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree046.table
  base := (-598110344390482860830031462336750671611/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-20151792517783687961410852217280729800000000000000)
      constant := (263746390765114918104044158765200896632813489063072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree046.table
  base := (-957040241881897923413093059306761965511/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-40313317020718936390564593050680619600000000000000)
      constant := (527751532039799581563072295355824612423942348644840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334877741255184753601/100000000000000000000)
  centralHi := (167438870627592376801/50000000000000000000)
  directionLo := (84644540030779644631/25000000000000000000)
  directionHi := (13543126404924743141/4000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree047.table
  base := (-9029449470988994725294312335749091117679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-20551557080022440079416343814544207400000000000000)
      constant := (274627675143381600588762608139458246190217250787938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree047.table
  base := (-4515014891529819090280132871962960995909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-41113057710091039767178682519471034800000000000000)
      constant := (549525012157608875976351735821703510817397514955992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84644540030779644631/25000000000000000000)
  centralHi := (13543126404924743141/4000000000000000000)
  directionLo := (68447714187264947243/20000000000000000000)
  directionHi := (42779821367040592027/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree048.table
  base := (-8451038562506510030249407942194815262599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-20951321642261192197421835411807685000000000000000)
      constant := (285729572432896187334872100353309464529619936496178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree048.table
  base := (-4225783577811241889190461758790338386167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-41912798399463143143792771988261450000000000000000)
      constant := (571739939109566179836294265765500991786310962490696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68447714187264947243/20000000000000000000)
  centralHi := (42779821367040592027/12500000000000000000)
  directionLo := (345860243972503195961/100000000000000000000)
  directionHi := (172930121986251597981/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree049.table
  base := (-7835084139949468188640690953878956063691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-21351086204499944315427327009071162600000000000000)
      constant := (297051944729272246276147674340166203348642704172202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree049.table
  base := (-783556549000283649375189878808061438183/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-42712539088835246520406861457051865200000000000000)
      constant := (594396037287821142977343542420408440998409157260520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345860243972503195961/100000000000000000000)
  centralHi := (172930121986251597981/50000000000000000000)
  directionLo := (87361095919787533361/25000000000000000000)
  directionHi := (69888876735830026689/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree050.table
  base := (-7182076425279556293707694112362607556073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-21750850766738696433432818606334640200000000000000)
      constant := (308594669418693727081672467461511663682659943546606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree050.table
  base := (-7182514637111460661336227886218256470957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-43512279778207349897020950925842280400000000000000)
      constant := (617493061650355419910330028543556467563084696956108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87361095919787533361/25000000000000000000)
  centralHi := (69888876735830026689/20000000000000000000)
  directionLo := (352992133352972531953/100000000000000000000)
  directionHi := (176496066676486265977/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree051.table
  base := (-811556427974921458098095516735200560473/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-22150615328977448551438310203598117800000000000000)
      constant := (320357637447959941529189033276383282538515728347248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree051.table
  base := (-649285025983284930282453161927446527751/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-44312020467579453273635040394632695600000000000000)
      constant := (641030794262058166781986944317939823036585424830440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352992133352972531953/100000000000000000000)
  centralHi := (176496066676486265977/50000000000000000000)
  directionLo := (356504579400131125263/100000000000000000000)
  directionHi := (22281536212508195329/6250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree052.table
  base := (-360412314831396077273184045889177818263/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-22550379891216200669443801800861595400000000000000)
      constant := (332340751795470754307198710028610117985372619276576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree052.table
  base := (-5766959944271179511885329516162138527913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-45111761156951556650249129863423110800000000000000)
      constant := (665009041237648856039915528992869036558207951934172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356504579400131125263/100000000000000000000)
  centralHi := (22281536212508195329/6250000000000000000)
  directionLo := (1439931020889242751/400000000000000000)
  directionHi := (359982755222310687751/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree053.table
  base := (-5004858470242878743421213981199220301433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47192260000000000000000000000000000000000000000
      center := (308990299)
      previous := (0)
      next := (276193725)
      square := (7142430841666986760867819134409600000000000000)
      linear := (-433021593461414203536779120719341000000000000000)
      constant := (6500828794698883460439578485431347103373749549142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree053.table
  base := (-5005188604093081547382760441059420670161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94384520000000000000000000000000000000000000000
      center := (618144123)
      previous := (0)
      next := (552223925)
      square := (14284861683333973521735638268819200000000000000)
      linear := (-866254751817427547676664515702142000000000000000)
      constant := (13008068491287167850905921412475990028856877569228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1439931020889242751/400000000000000000)
  centralHi := (359982755222310687751/100000000000000000000)
  directionLo := (181713822384008330283/50000000000000000000)
  directionHi := (363427644768016660567/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree054.table
  base := (-4207543013314240739455741787379475322947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-23349909015693704905454784995388550600000000000000)
      constant := (356967083559436005578255351173216072684048276411834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree054.table
  base := (-4207843262361509173068747902042000998657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-46711242535695763403477308801003941200000000000000)
      constant := (714286407079181830106180092816266995644281863574908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181713822384008330283/50000000000000000000)
  centralHi := (363427644768016660567/100000000000000000000)
  directionLo := (73368037156737227913/20000000000000000000)
  directionHi := (183420092891843069783/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree055.table
  base := (-3374924278368612302698707693186827817291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-23749673577932457023460276592652028200000000000000)
      constant := (369610155681139462612763590523135982188277204351402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree055.table
  base := (-421899660599944032379429092521686024063/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-47510983225067866780091398269794356400000000000000)
      constant := (739585235612624099125795104791989828431191664518176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73368037156737227913/20000000000000000000)
  centralHi := (183420092891843069783/50000000000000000000)
  directionLo := (370221272795055656179/100000000000000000000)
  directionHi := (18511063639752782809/5000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree056.table
  base := (-626811487377391747049158664967982719897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-24149438140171209141465768189915505800000000000000)
      constant := (382473081534132253843086314712099578037510808378936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree056.table
  base := (-626873532329054113154899798287631328689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-48310723914439970156705487738584771600000000000000)
      constant := (765323993851659930137842660997717583016220201921264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370221272795055656179/100000000000000000000)
  centralHi := (18511063639752782809/5000000000000000000)
  directionLo := (186785879922822774499/50000000000000000000)
  directionHi := (373571759845645548999/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree057.table
  base := (-802362553624559724639909937700054701519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-24549202702409961259471259787178983400000000000000)
      constant := (395555806822458570447411525511016699270023945344836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree057.table
  base := (-6269338549557897282819790671577592479/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-49110464603812073533319577207375186800000000000000)
      constant := (791502573308295485042998291496164200107783441171456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186785879922822774499/50000000000000000000)
  centralHi := (373571759845645548999/100000000000000000000)
  directionLo := (376892463016115947157/100000000000000000000)
  directionHi := (188446231508057973579/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree058.table
  base := (-667555175695159002977634780201943868773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-24948967264648713377476751384442461000000000000000)
      constant := (408858283167078226588026718539224461215929131126006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree058.table
  base := (-667760136352846147679541445543191984003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-49910205293184176909933666676165602000000000000000)
      constant := (818120877319828967974242655868808671682206754582132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376892463016115947157/100000000000000000000)
  centralHi := (188446231508057973579/50000000000000000000)
  directionLo := (380184162745551490569/100000000000000000000)
  directionHi := (38018416274555149057/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree059.table
  base := (304091463314544535156472646542697449767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-25348731826887465495482242981705938600000000000000)
      constant := (422380467452022133516866416883794229944498928378126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree059.table
  base := (18994078796530825716205251066551102849/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-50709945982556280286547756144956017200000000000000)
      constant := (845178819741812095524297807573241731448539672586304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380184162745551490569/100000000000000000000)
  centralHi := (38018416274555149057/10000000000000000000)
  directionLo := (191723802986690750623/50000000000000000000)
  directionHi := (383447605973381501247/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree060.table
  base := (1310061150503822492567048057516573312173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-25748496389126217613487734578969416200000000000000)
      constant := (436122321244189175705795433655049360034902785719194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree060.table
  base := (261978404734320946944505957716149268717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-51509686671928383663161845613746432400000000000000)
      constant := (872676323788252079632285825085570616191869434112260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191723802986690750623/50000000000000000000)
  centralHi := (383447605973381501247/100000000000000000000)
  directionLo := (386683508118589525677/100000000000000000000)
  directionHi := (193341754059294762839/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree061.table
  base := (2350216889873879065063106706404749933283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-26148260951364969731493226176232893800000000000000)
      constant := (450083810278280144259038831631427970982658312144774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree061.table
  base := (2350063303352771984303976742757305263927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-52309427361300487039775935082536847600000000000000)
      constant := (900613321002047003418122924225993276189294883013212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386683508118589525677/100000000000000000000)
  centralHi := (193341754059294762839/50000000000000000000)
  directionLo := (48736569363883623571/12500000000000000000)
  directionHi := (389892554911068988569/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree062.table
  base := (3424436519893570433221360383393124496649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-26548025513603721849498717773496371400000000000000)
      constant := (464264903999377718569311441416491909821328612304722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree062.table
  base := (856074268204249804032271267948902485637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-53109168050672590416390024551327262800000000000000)
      constant := (928989750340674319099508558089415764617433488951888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48736569363883623571/12500000000000000000)
  centralHi := (389892554911068988569/100000000000000000000)
  directionLo := (196537702044202323919/50000000000000000000)
  directionHi := (393075404088404647839/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree063.table
  base := (4532611088764990887371484817600506032451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-26947790075842473967504209370759849000000000000000)
      constant := (478665575156569555197970156786679777906119478955078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree063.table
  base := (4532484503445971458663530053522431145951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-53908908740044693793004114020117678000000000000000)
      constant := (957805557363928446490918197892977877406601265916156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196537702044202323919/50000000000000000000)
  centralHi := (393075404088404647839/100000000000000000000)
  directionLo := (396232686969972552007/100000000000000000000)
  directionHi := (49529085871246569001/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree064.table
  base := (2837321705239683734155840578095970476601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-27347554638081226085509700968023326600000000000000)
      constant := (493285799441790463953425388117158924243051230067556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree064.table
  base := (2837264260970987698147228585070935025489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-54708649429416797169618203488908093200000000000000)
      constant := (987060693512061355303875686405372028504318850520968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396232686969972552007/100000000000000000000)
  centralHi := (49529085871246569001/12500000000000000000)
  directionLo := (399365009919028723937/100000000000000000000)
  directionHi := (199682504959514361969/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree065.table
  base := (6850446781111899939823820753727223617653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-27747319200319978203515192565286804200000000000000)
      constant := (508125555168743385211740098486059320237024831118634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree065.table
  base := (3425171263734154405446975524857957074853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-55508390118788900546232292957698508400000000000000)
      constant := (1016755115464047505731004049094398966774920407440936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399365009919028723937/100000000000000000000)
  centralHi := (199682504959514361969/50000000000000000000)
  directionLo := (25154559731398566149/6250000000000000000)
  directionHi := (80494591140475411677/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree066.table
  base := (2014985959301407459549037307230280503239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-28147083762558730321520684162550281800000000000000)
      constant := (523184822987359529974982253800946881330493857478968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree066.table
  base := (8059849250816138132997398550005647755569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-56308130808161003922846382426488923600000000000000)
      constant := (1046888784566895809130370123867454359771701824176964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25154559731398566149/6250000000000000000)
  centralHi := (80494591140475411677/20000000000000000000)
  directionLo := (405557084756251324913/100000000000000000000)
  directionHi := (202778542378125662457/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree067.table
  base := (232576638505141323180783791376292085833/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-28546848324797482439526175759813759400000000000000)
      constant := (538463585629786102998706311046005767822521529546960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree067.table
  base := (9302979739562932180160125072857123581213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-57107871497533107299460471895279338800000000000000)
      constant := (1077461666327987357254921523620472555530305391120628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405557084756251324913/100000000000000000000)
  centralHi := (202778542378125662457/50000000000000000000)
  directionLo := (408617936366198780251/100000000000000000000)
  directionHi := (102154484091549695063/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree068.table
  base := (42319001091049806125565848408549582147/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-28946612887036234557531667357077237000000000000000)
      constant := (553961827684354615853113778582630184287233671441500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree068.table
  base := (2115934491008992995572829132982703778901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-57907612186905210676074561364069754000000000000000)
      constant := (1108473729963346792851821263475147581708554560831780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408617936366198780251/100000000000000000000)
  centralHi := (102154484091549695063/25000000000000000000)
  directionLo := (411656029768000034451/100000000000000000000)
  directionHi := (102914007442000008613/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree069.table
  base := (11889943034358497026408744310669374148267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-29346377449274986675537158954340714600000000000000)
      constant := (569679535394391834807617064219218225832864162511126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree069.table
  base := (185779257321900486824258129315810163261/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-58707352876277314052688650832860169200000000000000)
      constant := (1139924947995573208873379602706471417691437371809024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411656029768000034451/100000000000000000000)
  centralHi := (102914007442000008613/25000000000000000000)
  directionLo := (414671865175989707341/100000000000000000000)
  directionHi := (207335932587994853671/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree070.table
  base := (2646718945030623915764081216985240887679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-29746142011513738793542650551604192200000000000000)
      constant := (585616696479095791560635024170749676209550421360310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree070.table
  base := (1323353074599002267440205055789611692623/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-59507093565649417429302740301650584400000000000000)
      constant := (1171815295895877158992958799285429762441514297985880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414671865175989707341/100000000000000000000)
  centralHi := (207335932587994853671/50000000000000000000)
  directionLo := (104416481186136223931/25000000000000000000)
  directionHi := (16706636989781795829/4000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree071.table
  base := (3652665377052740518077147439817066219157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-30145906573752490911548142148867669800000000000000)
      constant := (601773299974017015938169208754745287563775491446184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree071.table
  base := (1461060351013838156668777114697213195283/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-60306834255021520805916829770440999600000000000000)
      constant := (1204144751765305747341258259210267606127045967615480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104416481186136223931/25000000000000000000)
  centralHi := (16706636989781795829/4000000000000000000)
  directionLo := (210319336733987381053/50000000000000000000)
  directionHi := (420638673467974762107/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree072.table
  base := (16021104241400045925171636086865786618413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-30545671135991243029553633746131147400000000000000)
      constant := (618149336088965460716246509459483748372163535541914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree072.table
  base := (16021051673527592760089131451114252674187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-61106574944393624182530919239231414800000000000000)
      constant := (1236913296050798306682971272528685379880202838841772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210319336733987381053/50000000000000000000)
  centralHi := (420638673467974762107/100000000000000000000)
  directionLo := (423590560023567038343/100000000000000000000)
  directionHi := (52948820002945879793/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree073.table
  base := (8732443985617413085380173085361716186233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-30945435698229995147559125343394625000000000000000)
      constant := (634744796081411043850035584572329857600653311259748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree073.table
  base := (349296806649581308534481288314245916117/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-61906315633765727559145008708021830000000000000000)
      constant := (1270120911292210001861397766208229945237985776842600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423590560023567038343/100000000000000000000)
  centralHi := (52948820002945879793/12500000000000000000)
  directionLo := (21326100878105965013/5000000000000000000)
  directionHi := (426522017562119300261/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree074.table
  base := (9470990740906767389640191951300743961651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-31345200260468747265564616940658102600000000000000)
      constant := (651559672143664317771531201195702200550655638625356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree074.table
  base := (236774228956263836622748425264007904869/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-62706056323137830935759098176812245200000000000000)
      constant := (1303767581896877781036938316355424436925960880621120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21326100878105965013/5000000000000000000)
  centralHi := (426522017562119300261/100000000000000000000)
  directionLo := (214716732224949378571/50000000000000000000)
  directionHi := (429433464449898757143/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree075.table
  base := (5113089223192882187679113530848186636011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-31744964822707499383570108537921580200000000000000)
      constant := (668593957302316971706234679720036535283209317267032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree075.table
  base := (10226158893309073190565699756947203415991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-63505797012509934312373187645602660400000000000000)
      constant := (1337853293938689407494524059328074180423463111108792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214716732224949378571/50000000000000000000)
  centralHi := (429433464449898757143/100000000000000000000)
  directionLo := (54040663120703624369/12500000000000000000)
  directionHi := (432325304965628994953/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree076.table
  base := (21995989300855451850347196537801621073073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-32144729384946251501575600135185057800000000000000)
      constant := (685847645328592727317647585393503751329540282079394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree076.table
  base := (21995953877290095804950301880726824998007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-64305537701882037688987277114393075600000000000000)
      constant := (1372378034978957932789126477966007528231372725753692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54040663120703624369/12500000000000000000)
  centralHi := (432325304965628994953/100000000000000000000)
  directionLo := (435197929955791229727/100000000000000000000)
  directionHi := (13599935311118475929/3125000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree077.table
  base := (23572856460327447490620124734006566584141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-32544493947185003619581091732448535400000000000000)
      constant := (703320730658410367060180722793420156754314297927898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree077.table
  base := (2946603047141676085538482333110652091739/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-65105278391254141065601366583183490800000000000000)
      constant := (1407341793906706251679066219231537230993589134763872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435197929955791229727/100000000000000000000)
  centralHi := (13599935311118475929/3125000000000000000)
  directionLo := (43805171745124732959/10000000000000000000)
  directionHi := (438051717451247329591/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree078.table
  base := (1573933656121485387740744336844318546667/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-32944258509423755737586583329712013000000000000000)
      constant := (721013208321094474772089093562004997749980725541216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree078.table
  base := (25182909444190350226726177325797242863977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-65905019080626244442215456051973906000000000000000)
      constant := (1442744560796233983873364057984979734690711440511012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43805171745124732959/10000000000000000000)
  centralHi := (438051717451247329591/100000000000000000000)
  directionLo := (1102217583119846961/250000000000000000)
  directionHi := (440887033247938784401/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree079.table
  base := (26826217658726085206419545631647087743173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-33344023071662507855592074926975490600000000000000)
      constant := (738925073875788017946578796583219003767998757237194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree079.table
  base := (26826191351966822507784257290572605945481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-66704759769998347818829545520764321200000000000000)
      constant := (1478586326780075954780243790416277567917760862876836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1102217583119846961/250000000000000000)
  centralHi := (440887033247938784401/100000000000000000000)
  directionLo := (2218521157270934919/500000000000000000)
  directionHi := (443704231454186983801/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree080.table
  base := (28502678079163887730916083338575134981473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-33743787633901259973597566524238968200000000000000)
      constant := (757056323354725958637534141782489226737778075694594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree080.table
  base := (28502654262878979178924755058187150221733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-67504500459370451195443634989554736400000000000000)
      constant := (1514867083935671593123685027463688523092384662697748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2218521157270934919/500000000000000000)
  centralHi := (443704231454186983801/100000000000000000000)
  directionLo := (446503655006913004801/100000000000000000000)
  directionHi := (223251827503456502401/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree081.table
  base := (30212305584858649030913550268472959284381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-34143552196140012091603058121502445800000000000000)
      constant := (775406953212622224070670855592079209571844987082618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree081.table
  base := (7553071006530282964279321283109354544877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-68304241148742554572057724458345151600000000000000)
      constant := (1551586825184250785593787704000699736868034323005648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446503655006913004801/100000000000000000000)
  centralHi := (223251827503456502401/50000000000000000000)
  directionLo := (449285636158907314429/100000000000000000000)
  directionHi := (44928563615890731443/10000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree082.table
  base := (15977543754975446444658780937805187940931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-34543316758378764209608549718765923400000000000000)
      constant := (793976960281504986562953984419871924191767172177036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree082.table
  base := (31955067997297642413945029458199545058847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-69103981838114657948671813927135566800000000000000)
      constant := (1588745544200606903317876925447392151810367522996732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449285636158907314429/100000000000000000000)
  centralHi := (44928563615890731443/10000000000000000000)
  directionLo := (452050496939109335321/100000000000000000000)
  directionHi := (226025248469554667661/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree083.table
  base := (3373101253596429761936139928062142736837/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-34943081320617516327614041316029401000000000000000)
      constant := (812766341730408516016890200415347052043277933925860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree083.table
  base := (33730994877454492691636333151780526813877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-69903722527486761325285903395925982000000000000000)
      constant := (1626343235332574283314722113650009761843977022915412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452050496939109335321/100000000000000000000)
  centralHi := (226025248469554667661/50000000000000000000)
  directionLo := (90959709917540382051/20000000000000000000)
  directionHi := (28424909349231369391/6250000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree084.table
  base := (35540070547961239927183212629243468961711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-35342845882856268445619532913292878600000000000000)
      constant := (831775095029394951560469784019766971469877876451358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree084.table
  base := (35540054569406321604278174007566809574661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-70703463216858864701899992864716397200000000000000)
      constant := (1664379893529157559201584197986633831055069648032916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90959709917540382051/20000000000000000000)
  centralHi := (28424909349231369391/6250000000000000000)
  directionLo := (114382524241921187007/25000000000000000000)
  directionHi := (457530096967684748029/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree085.table
  base := (3738225250613525273554043255901962150297/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-35742610445095020563625024510556356200000000000000)
      constant := (851003217917437138330542176726099856287269680364660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree085.table
  base := (4672779756185712889610492201890589995951/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-71503203906230968078514082333506812400000000000000)
      constant := (1702855514276375782154940289977228873601668612129248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114382524241921187007/25000000000000000000)
  centralHi := (457530096967684748029/100000000000000000000)
  directionLo := (460245432954462529257/100000000000000000000)
  directionHi := (230122716477231264629/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree086.table
  base := (39257550331171174688994740100501147655127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-36142375007333772681630516107819833800000000000000)
      constant := (870450708373745025228980051451669175089327461700206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree086.table
  base := (39257537253046642576737379671270971337947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-72302944595603071455128171802297227600000000000000)
      constant := (1741770093539986923946128685723573837874229192516332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460245432954462529257/100000000000000000000)
  centralHi := (230122716477231264629/50000000000000000000)
  directionLo := (462944842804866245097/100000000000000000000)
  directionHi := (231472421402433122549/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree087.table
  base := (41165956801886226651862573818365419920163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-36542139569572524799636007705083311400000000000000)
      constant := (890117564592163755587166512478871819185972011153414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree087.table
  base := (41165944972236635148175227979380160924367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-73102685284975174831742261271087642800000000000000)
      constant := (1781123627714349580406677074037757202297756418673852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462944842804866245097/100000000000000000000)
  centralHi := (231472421402433122549/50000000000000000000)
  directionLo := (465628603506919420913/100000000000000000000)
  directionHi := (232814301753459710457/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree088.table
  base := (21553732731913730385602769690198825905787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-36941904131811276917641499302346789000000000000000)
      constant := (910003784958312154539037314320373233704710737451372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree088.table
  base := (4310745476471375511559027851013721351607/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-73902425974347278208356350739878058000000000000000)
      constant := (1820916113576759794763506269877279429568814429952920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465628603506919420913/100000000000000000000)
  centralHi := (232814301753459710457/50000000000000000000)
  directionLo := (234148492055781574119/50000000000000000000)
  directionHi := (468296984111563148239/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree089.table
  base := (45082070547645283895558537537215522651807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-37341668694050029035646990899610266600000000000000)
      constant := (930109368029166398120832207149249345466405816693246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree089.table
  base := (45082060872129421582532935381666779821633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-74702166663719381584970440208668473200000000000000)
      constant := (1861147548246673042973475679741165177511075736502148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234148492055781574119/50000000000000000000)
  centralHi := (468296984111563148239/100000000000000000000)
  directionLo := (235475123023732213191/50000000000000000000)
  directionHi := (470950246047464426383/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree090.table
  base := (47089766896191085856464360811790140449173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-37741433256288781153652482496873744200000000000000)
      constant := (950434312514825746563096266394611729529623611705194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree090.table
  base := (47089758147325740863136052819739225559371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-75501907353091484961584529677458888400000000000000)
      constant := (1901817929149285581089901816539759776396842705685676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235475123023732213191/50000000000000000000)
  centralHi := (470950246047464426383/100000000000000000000)
  directionLo := (236794321709975204287/50000000000000000000)
  directionHi := (18943545736798016343/4000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree091.table
  base := (49130549899401196188791780722944890919141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-38141197818527533271657974094137221800000000000000)
      constant := (970978617262225786094162084552863998892017027557898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree091.table
  base := (12282635497327612550297390423675060026813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-76301648042463588338198619146249303600000000000000)
      constant := (1942927253983006444019803228985026254893960961256912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236794321709975204287/50000000000000000000)
  centralHi := (18943545736798016343/4000000000000000000)
  directionLo := (476212423295036048647/100000000000000000000)
  directionHi := (59526552911879506081/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree092.table
  base := (12801103859032758878686225647430178925451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-38540962380766285389663465691400699400000000000000)
      constant := (991742281240590046329815476553809037816763769236312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree092.table
  base := (12801102071293516575114525416801551942559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-77101388731835691714812708615039718800000000000000)
      constant := (1984475520690402198626054997925887896305494174277616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476212423295036048647/100000000000000000000)
  centralHi := (59526552911879506081/12500000000000000000)
  directionLo := (478821825969443718657/100000000000000000000)
  directionHi := (239410912984721859329/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree093.table
  base := (26655679911096911611354004943645247415527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-38940726943005037507668957288664177000000000000000)
      constant := (1012725303528433494942368904451519375431257509142812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree093.table
  base := (53311353358204278398891463694922238484147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-77901129421207795091426798083830134000000000000000)
      constant := (2026462727432241793773012324421634377758254233683532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478821825969443718657/100000000000000000000)
  centralHi := (239410912984721859329/50000000000000000000)
  directionLo := (481417085227450046723/100000000000000000000)
  directionHi := (120354271306862511681/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree094.table
  base := (13862844940984698476892993436164037996521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-39340491505243789625674448885927654600000000000000)
      constant := (1033927683301951568599778716954310679046172000302152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree094.table
  base := (55451373921533161661559843149984311057183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-78700870110579898468040887552620549200000000000000)
      constant := (2068888872564309137099288285601743660645313423037948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481417085227450046723/100000000000000000000)
  centralHi := (120354271306862511681/25000000000000000000)
  directionLo := (483998428585336996717/100000000000000000000)
  directionHi := (241999214292668498359/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree095.table
  base := (57624472316775662372800262822229788218861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-39740256067482541743679940483191132200000000000000)
      constant := (1055349419824646354539958667703860252435457953644058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree095.table
  base := (57624467036724523299685402573505646978177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-79500610799952001844654977021410964400000000000000)
      constant := (2111753954616686913687802716317681988848820839086212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483998428585336996717/100000000000000000000)
  centralHi := (241999214292668498359/50000000000000000000)
  directionLo := (48656607752417061789/10000000000000000000)
  directionHi := (486566077524170617891/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree096.table
  base := (59830634848116036888765049803152849576711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-40140020629721293861685432080454609800000000000000)
      constant := (1076990512438057534728830592211314951913914687921358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree096.table
  base := (59830630076772606846440907584145559521941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-80300351489324105221269066490201379600000000000000)
      constant := (2155057972275247133523356179037394572701732102992596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48656607752417061789/10000000000000000000)
  centralHi := (486566077524170617891/100000000000000000000)
  directionLo := (489120247711581519421/100000000000000000000)
  directionHi := (244560123855790759711/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree097.table
  base := (12413973000851895699389788962904652651187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-40539785191960045979690923677718087400000000000000)
      constant := (1098850960553479960855938736526436961137799414634430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree097.table
  base := (62069860693040334822724808802364200708583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-81100092178696208597883155958991794800000000000000)
      constant := (2198800924365112385581989281982827330430035311576348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489120247711581519421/100000000000000000000)
  centralHi := (244560123855790759711/50000000000000000000)
  directionLo := (491661149213175599523/100000000000000000000)
  directionHi := (122915287303293899881/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree098.table
  base := (64342160680802708487911477372367568724077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-40939549754198798097696415274981565000000000000000)
      constant := (1120930763644562435550628691219935672779610903233306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree098.table
  base := (64342156785716034409876878167568407535163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-81899832868068311974497245427782210000000000000000)
      constant := (2242982809835877170667954674010455294025564937246828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491661149213175599523/100000000000000000000)
  centralHi := (122915287303293899881/25000000000000000000)
  directionLo := (247094493347080772367/50000000000000000000)
  directionHi := (98837797338832308947/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree099.table
  base := (66647519996195758493277637084456599542873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-41339314316437550215701906872245042600000000000000)
      constant := (1143229921240693603668670171171767348588018661943794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree099.table
  base := (16661879119353211553302950145980553913371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-82699573557440415351111334896572625200000000000000)
      constant := (2287603627748401323616395575833521536571490040438704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247094493347080772367/50000000000000000000)
  centralHi := (98837797338832308947/20000000000000000000)
  directionLo := (496703959611742808549/100000000000000000000)
  directionHi := (9934079192234856171/2000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree100.table
  base := (8623242658513655409584325310074123236093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-41739078878676302333707398469508520200000000000000)
      constant := (1165748432921090958715373317848829764964461070983632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree100.table
  base := (13797187617915073578297987867512714395859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-83499314246812518727725424365363040400000000000000)
      constant := (2332663377263007720927372657076101147766981405121020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496703959611742808549/100000000000000000000)
  centralHi := (9934079192234856171/2000000000000000000)
  directionLo := (499206262398785904921/100000000000000000000)
  directionHi := (249603131199392952461/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree101.table
  base := (7135742299231295303012299860126352365737/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-42138843440915054451712890066771997800000000000000)
      constant := (1188486298309517977936840753741170687920860206567860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree101.table
  base := (14271484024278813976466827137297194129443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-84299054936184622104339513834153455600000000000000)
      constant := (2378162057628934471187280793348005261779238828692540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499206262398785904921/100000000000000000000)
  centralHi := (249603131199392952461/50000000000000000000)
  directionLo := (250848042319621831291/50000000000000000000)
  directionHi := (501696084639243662583/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree102.table
  base := (1844049095594952190896928831577943965329/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-42538608003153806569718381664035475400000000000000)
      constant := (1211443517069562434846615651658367473227974276550480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree102.table
  base := (73761961230960117333538120328066037754811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-85098795625556725480953603302943870800000000000000)
      constant := (2424099668174907841711310758402904016609485483806316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250848042319621831291/50000000000000000000)
  centralHi := (501696084639243662583/100000000000000000000)
  directionLo := (4033388889886250843/800000000000000000)
  directionHi := (31510850702236334711/6250000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree103.table
  base := (76199562559904114720384611983455964316599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-42938372565392558687723873261298953000000000000000)
      constant := (1234620088900416106206489157455815746627872210315822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree103.table
  base := (76199560218421865254335431684068889940289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-85898536314928828857567692771734286000000000000000)
      constant := (2470476208300716498106043898627548660116919131409284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4033388889886250843/800000000000000000)
  centralHi := (31510850702236334711/6250000000000000000)
  directionLo := (15832469455313285853/3125000000000000000)
  directionHi := (506639022570025147297/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree104.table
  base := (78670218125236804132739084663267707382827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-43338137127631310805729364858562430600000000000000)
      constant := (1258016013533102486224019804080179499710995743990806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree104.table
  base := (78670216010929840383856360092968550487893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-86698277004300932234181782240524701200000000000000)
      constant := (2517291677469680412771786095678543985868346397066708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15832469455313285853/3125000000000000000)
  centralHi := (506639022570025147297/100000000000000000000)
  directionLo := (509092494655825883221/100000000000000000000)
  directionHi := (254546247327912941611/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree105.table
  base := (81173929558186809712360751338827759294057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-43737901689870062923734856455825908200000000000000)
      constant := (1281631290727104828002275143074707781247659538313746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree105.table
  base := (81173927649179819163609422295881299326609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-87498017693673035610795871709315116400000000000000)
      constant := (2564546075201919201733470523527057782893767062571204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509092494655825883221/100000000000000000000)
  centralHi := (254546247327912941611/50000000000000000000)
  directionLo := (511534199285906748579/100000000000000000000)
  directionHi := (25576709964295337429/5000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree106.table
  base := (16742139199775706763930492294669262843661/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47192260000000000000000000000000000000000000000
      center := (308990299)
      previous := (0)
      next := (276193725)
      square := (7142430841666986760867819134409600000000000000)
      linear := (-832786155700166321542270717982818600000000000000)
      constant := (24631432457874564638726413638026916483063194631930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree106.table
  base := (83710694275383955297035411311737276700669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94384520000000000000000000000000000000000000000
      center := (618144123)
      previous := (0)
      next := (552223925)
      square := (14284861683333973521735638268819200000000000000)
      linear := (-1665995441189530924290753984492557200000000000000)
      constant := (49287535869213864642982344049809410072749982724388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511534199285906748579/100000000000000000000)
  centralHi := (25576709964295337429/5000000000000000000)
  directionLo := (20558572166889622403/4000000000000000000)
  directionHi := (128491076043060140019/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree107.table
  base := (10785064584799648394901681601997520884717/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-44537430814347567159745839650352863400000000000000)
      constant := (1329519901961523598507043164547733994682752574873808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree107.table
  base := (43140257561259034306117735582918506115229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-89097499072417242364024050646895946800000000000000)
      constant := (2660371654685232677713800816665544787977311310863848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20558572166889622403/4000000000000000000)
  centralHi := (128491076043060140019/25000000000000000000)
  directionLo := (516382973080481295267/100000000000000000000)
  directionHi := (129095743270120323817/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree108.table
  base := (3555335636366327311913751780447680498827/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-44937195376586319277751331247616341000000000000000)
      constant := (1353793235637641891793620747296372388020928485970150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree108.table
  base := (17776677900941883210681159215540167131797/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-89897239761789345740638140115686362000000000000000)
      constant := (2708942835709513177578331779863347810309542569434660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516382973080481295267/100000000000000000000)
  centralHi := (129095743270120323817/25000000000000000000)
  directionLo := (259395182979377396971/50000000000000000000)
  directionHi := (518790365958754793943/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree109.table
  base := (91519318076297489897105378728099401773937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-45336959938825071395756822844879818600000000000000)
      constant := (1378285921141917642709962048414427638729108509476386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree109.table
  base := (91519316808643736418906863508297926189111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-90696980451161449117252229584476777200000000000000)
      constant := (2757952943834373253262498865629567092835879756097116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259395182979377396971/50000000000000000000)
  centralHi := (518790365958754793943/100000000000000000000)
  directionLo := (521186639061095252641/100000000000000000000)
  directionHi := (260593319530547626321/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree110.table
  base := (18837659525994901483047167485146353333843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-45736724501063823513762314442143296200000000000000)
      constant := (1402997958336825282060595729088632326131438519862270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree110.table
  base := (18837659297176656139781676354484786135567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-91496721140533552493866319053267192400000000000000)
      constant := (2807401978785463526208383544944712214497765874905260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521186639061095252641/100000000000000000000)
  centralHi := (260593319530547626321/50000000000000000000)
  directionLo := (261785972532898539677/50000000000000000000)
  directionHi := (104714389013159415871/20000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree111.table
  base := (19378065815698113652261147505499026240991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-46136489063302575631767806039406773800000000000000)
      constant := (1427929347099381641748776286447749369241959253135990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree111.table
  base := (96890328045999076813825917337198646821491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-92296461829905655870480408522057607600000000000000)
      constant := (2857289940317452809859713431448877324101948554712396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261785972532898539677/50000000000000000000)
  centralHi := (104714389013159415871/20000000000000000000)
  directionLo := (262973216594467890637/50000000000000000000)
  directionHi := (21037857327557431251/4000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree112.table
  base := (99625411982136499252812457648674589955313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-46536253625541327749773297636670251400000000000000)
      constant := (1453080087319607112760871157348712931094191953230114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree112.table
  base := (996254110504309802661019661358435111789/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-93096202519277759247094497990848022800000000000000)
      constant := (2907616828210956673949965712315235425567996086328400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262973216594467890637/50000000000000000000)
  centralHi := (21037857327557431251/4000000000000000000)
  directionLo := (528310249293296736009/100000000000000000000)
  directionHi := (52831024929329673601/10000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree113.table
  base := (102393545947691874667713728465359131407343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-46936018187780079867778789233933729000000000000000)
      constant := (1478450178899149804086558217315425638525572332855454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree113.table
  base := (163829672171197221653374129145777843581/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-93895943208649862623708587459638438000000000000000)
      constant := (2958382642269791432960753223910287886164404475272500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528310249293296736009/100000000000000000000)
  centralHi := (52831024929329673601/10000000000000000000)
  directionLo := (265331767996468432311/50000000000000000000)
  directionHi := (530663535992936864623/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree114.table
  base := (52597365311753414847416315448506979918951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-47335782750018831985784280831197206600000000000000)
      constant := (1504039621750055410925427732370275428736389093904156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree114.table
  base := (105194729864991715368637947066385410468249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-94695683898021966000322676928428853200000000000000)
      constant := (3009587382318519027907525202956168677990857882659044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265331767996468432311/50000000000000000000)
  centralHi := (530663535992936864623/100000000000000000000)
  directionLo := (133251608188397827229/25000000000000000000)
  directionHi := (533006432753591308917/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree115.table
  base := (54014482847552325165202187110610701410621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-47735547312257584103789772428460684200000000000000)
      constant := (1529848415793667338966059764905387311810375365730676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree115.table
  base := (108028965010785562113852835472599406536173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-95495424587394069376936766397219268400000000000000)
      constant := (3061231048200251942826641825969477520882468221582388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133251608188397827229/25000000000000000000)
  centralHi := (533006432753591308917/100000000000000000000)
  directionLo := (107067815197825029483/20000000000000000000)
  directionHi := (66917384498640643427/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree116.table
  base := (110896250881249922465815150765818935068157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-48135311874496336221795264025724161800000000000000)
      constant := (1555876560959643273854201048349111437872295789183546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree116.table
  base := (22179250052782816165365489651034262280083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-96295165276766172753550855866009683600000000000000)
      constant := (3113313639774690577745446640666821857744783097151740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107067815197825029483/20000000000000000000)
  centralHi := (66917384498640643427/12500000000000000000)
  directionLo := (107532319830843780377/20000000000000000000)
  directionHi := (268830799577109450943/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree117.table
  base := (113796585930432889101121992071340869987621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-48535076436735088339800755622987639400000000000000)
      constant := (1582124057185075852211997501372080014965934637171338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree117.table
  base := (284491463433909081108061909647755419493/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-97094905966138276130164945334800098800000000000000)
      constant := (3165835156916368430521473942890401068614040350523200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107532319830843780377/20000000000000000000)
  centralHi := (268830799577109450943/50000000000000000000)
  directionLo := (4319793062667728253/800000000000000000)
  directionHi := (269987066416733015813/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree118.table
  base := (2334599412354518115365188411562631092313/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-48934840998973840457806247220251117000000000000000)
      constant := (1608590904413706401481149233089990037140017560805700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree118.table
  base := (1823905783053688707014759307797108103141/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-97894646655510379506779034803590514000000000000000)
      constant := (3218795599513083058209539830923527514944482625266944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4319793062667728253/800000000000000000)
  centralHi := (269987066416733015813/50000000000000000000)
  directionLo := (271138402413525366663/50000000000000000000)
  directionHi := (542276804827050733327/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree119.table
  base := (119696404741972567242239913725090619596821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-49334605561212592575811738817514594600000000000000)
      constant := (1635277102595221887168628504297107137455943640568938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree119.table
  base := (119696404288944211455366069486070785674189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-98694387344882482883393124272380929200000000000000)
      constant := (3272194967464493127986669142553019532746970387317684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271138402413525366663/50000000000000000000)
  centralHi := (542276804827050733327/100000000000000000000)
  directionLo := (272284870116582555761/50000000000000000000)
  directionHi := (544569740233165111523/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree120.table
  base := (30673972030818565785234292462293225307953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-49734370123451344693817230414778072200000000000000)
      constant := (1662182651684626252702037694954550759201395758528136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree120.table
  base := (122695887714704042280210177200678080840161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-99494128034254586260007213741171344400000000000000)
      constant := (3326033260680863957964335873785448967973484901350916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272284870116582555761/50000000000000000000)
  centralHi := (544569740233165111523/100000000000000000000)
  directionLo := (8544579086364314279/1562500000000000000)
  directionHi := (546853061527316113857/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree121.table
  base := (125728420600742659327145626685937493864373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-50134134685690096811822722012041549800000000000000)
      constant := (1689307551641678272374856438052823577312238245370794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree121.table
  base := (125728420232292452856123045144037706117907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-100293868723626689636621303209961759600000000000000)
      constant := (3380310479081945816065665799713046400195350492678092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8544579086364314279/1562500000000000000)
  centralHi := (546853061527316113857/100000000000000000000)
  directionLo := (549126888638664495413/100000000000000000000)
  directionHi := (274563444319332247707/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree122.table
  base := (128794002030489943670135988555967387288711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-50533899247928848929828213609305027400000000000000)
      constant := (1716651802430388873670290719761929993559982586257358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree122.table
  base := (32198500424560536253277488410296018473459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-101093609412998793013235392678752174800000000000000)
      constant := (3435026622595970914301258221234814059494405481639216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549126888638664495413/100000000000000000000)
  centralHi := (274563444319332247707/50000000000000000000)
  directionLo := (551391339023530449353/100000000000000000000)
  directionHi := (275695669511765224677/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree123.table
  base := (131892632283831661134151150488842651495939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-50933663810167601047833705206568505000000000000000)
      constant := (1744215404018571632210310019530429854819974433830342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree123.table
  base := (32973157996062182476415276815133210757271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-101893350102370896389849482147542590000000000000000)
      constant := (3490181691158756527449206118506078057217737828712304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551391339023530449353/100000000000000000000)
  centralHi := (275695669511765224677/50000000000000000000)
  directionLo := (553646527736193381983/100000000000000000000)
  directionHi := (17301453991756043187/3125000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree124.table
  base := (67512155622839816111616783228645530276781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-51333428372406353165839196803831982600000000000000)
      constant := (1771998356377440810159504880814593871814193041699636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree124.table
  base := (135024310975567501428787753115357685049233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-102693090791742999766463571616333005200000000000000)
      constant := (3545775684712902998265729196379793315277920075287748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553646527736193381983/100000000000000000000)
  centralHi := (17301453991756043187/3125000000000000000)
  directionLo := (555892567497106586987/100000000000000000000)
  directionHi := (138973141874276646747/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree125.table
  base := (138189038813104834350902901015181687823291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-51733192934645105283844688401095460200000000000000)
      constant := (1800000659481251905582005925495538603117676589516598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree125.table
  base := (13818903856957980918066811384317546383697/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-103492831481115103143077661085123420400000000000000)
      constant := (3601808603207076582826341550271864198579157790033320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555892567497106586987/100000000000000000000)
  centralHi := (138973141874276646747/25000000000000000000)
  directionLo := (558129568758641256001/100000000000000000000)
  directionHi := (279064784379320628001/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree126.table
  base := (70693407447026128961709324779873293481939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-52132957496883857401850179998358937800000000000000)
      constant := (1828222313306980213558446583364815434020393288276684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree126.table
  base := (141386814674511076555858916345437347413109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-104292572170487206519691750553913835600000000000000)
      constant := (3658280446595368154517170818773522852845995533765204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558129568758641256001/100000000000000000000)
  centralHi := (279064784379320628001/50000000000000000000)
  directionLo := (280178819884234161749/50000000000000000000)
  directionHi := (560357639768468323499/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree127.table
  base := (28923527881238330959860707858595155156433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-52532722059122609519855671595622415400000000000000)
      constant := (1856663317834033376565194159539958907342392260427370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree127.table
  base := (18077204901035551542004628668618462420713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-105092312859859309896305840022704250800000000000000)
      constant := (3715191214836719737040328688949146215331602265461024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280178819884234161749/50000000000000000000)
  centralHi := (560357639768468323499/100000000000000000000)
  directionLo := (140644221657670264393/25000000000000000000)
  directionHi := (562576886630681057573/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree128.table
  base := (29576302455177960080932804868139298920723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-52932486621361361637861163192885893000000000000000)
      constant := (1885323673043994327724981914846124815838438698905470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree128.table
  base := (73940756048747732473953208698453259992297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-105892053549231413272919929491494666000000000000000)
      constant := (3772540907894411687603284167838921127880166454049864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell131.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140644221657670264393/25000000000000000000)
  centralHi := (562576886630681057573/100000000000000000000)
  directionLo := (141196853341189012781/25000000000000000000)
  directionHi := (4518299306918048409/800000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 47239
  qDenominator := 89464
  table := BinomialMassData.Q47239_89464.Degree129.table
  base := (1511784334372914136594256215635099471973/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2501189780000000000000000000000000000000000000000
      center := (16376485847)
      previous := (0)
      next := (14638267425)
      square := (378548834608350298325994414123708800000000000000)
      linear := (-53332251183600113755866654790149370600000000000000)
      constant := (1914203378920391411438158883396608501060822640359400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47239_89464.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree129.table
  base := (30235686655299137774389184708243585941349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5002379560000000000000000000000000000000000000000
      center := (32761638519)
      previous := (0)
      next := (29267868025)
      square := (757097669216700596651988828247417600000000000000)
      linear := (-106691794238603516649534018960285081200000000000000)
      constant := (3830329525735604111980979033792376909607053798213220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell131.Kernel129
