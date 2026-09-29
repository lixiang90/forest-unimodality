import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell101.Parameters
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch000_049
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch050_099
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch100_149
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch150_199
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch000_049
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch050_099
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch100_149
import ForestUnimodality.BinomialMassData.Q22331_43056.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree000.table
  base := (92413979277656972595433871/1250000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (359377909994459815434808545000000000000)
      linear := (-15245021017697983796435057500000000000)
      constant := (369655917110627890381735484000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree000.table
  base := (92413979277656972595433871/1250000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (359377909994459815434808545000000000000)
      linear := (-15245021017697983796435057500000000000)
      constant := (369655917110627890381735484000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree001.table
  base := (102806202342153041906352194590191604110119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-935624648763308035739733563799888750000000000)
      constant := (496564665433651026533863131284026194208007430826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree001.table
  base := (410858315589843675337668630553474749773809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-1873264059934522511819748523005183750000000000)
      constant := (992245765394338103221993828899064383533201557043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49965205158052409469/100000000000000000000)
  directionHi := (4996520515805240947/10000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree002.table
  base := (243387437926853156632553988791007336552319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-3668900908357058400692139364119450000000000000)
      constant := (589434043470478817867285750768666124293074514813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree002.table
  base := (15188362488059490412447413117392830075881/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-1836465216586435640686351077465131250000000000)
      constant := (294268204324049113127404720539419771107963852696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49965205158052409469/100000000000000000000)
  centralHi := (4996520515805240947/10000000000000000000)
  directionLo := (14132294156254368327/20000000000000000000)
  directionHi := (17665367695317960409/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree003.table
  base := (12368681614016639919553554457674664199/800000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-101232454059027791294533548159983750000000000)
      constant := (6990805455998751438350556115353111665967493750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree003.table
  base := (30862757940393463764966672776833280172039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-608066311823468894547295087428371250000000000)
      constant := (41866843755304375251179129312526990545844379585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14132294156254368327/20000000000000000000)
  centralHi := (17665367695317960409/25000000000000000000)
  directionLo := (1730845478886986181/2000000000000000000)
  directionHi := (86542273944349309051/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree004.table
  base := (52689778831652251878522505024834692250607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-3632102065008971529558741918579397500000000000)
      constant := (130985502019348388952417234443012738191205942989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree004.table
  base := (105163671769603976926130376784083431373383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-7272263179649568820478609418780420000000000000)
      constant := (261466773724120250913522405306103947526718966741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1730845478886986181/2000000000000000000)
  centralHi := (86542273944349309051/100000000000000000000)
  directionLo := (49965205158052409469/50000000000000000000)
  directionHi := (99930410316104818939/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree005.table
  base := (1909269324259081683977203751986629547587/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-4530927870424192694165078036839233750000000000)
      constant := (98088916536251866604367099428468853553640708980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree005.table
  base := (19053486801479248066632532012281077315081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-4535964776443958795015781525352749375000000000)
      constant := (97912802886491729670168080439590210286178799974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49965205158052409469/50000000000000000000)
  centralHi := (99930410316104818939/100000000000000000000)
  directionLo := (111725595243128311219/100000000000000000000)
  directionHi := (5586279762156415561/5000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree006.table
  base := (11607126352092344261766033256284902779547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-1206611927964314190838092034466460000000000000)
      constant := (17453366598764053094218820335719204525914220205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree006.table
  base := (57918934729285654443021449378647916663243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-402651700967639494799426543801132500000000000)
      constant := (5808758027161419555966081155049655053860587443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111725595243128311219/100000000000000000000)
  centralHi := (5586279762156415561/5000000000000000000)
  directionLo := (24477851506141304009/20000000000000000000)
  directionHi := (61194628765353260023/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree007.table
  base := (22797292435758054513738844967858381252173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-6328579481254635023377750273358906250000000000)
      constant := (66570699086274931965610480271374148077163996071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree007.table
  base := (22752195666048187793871630819241966391219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-6335631149682307564568735157277828125000000000)
      constant := (66487579964452986481725495582193901113685735113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24477851506141304009/20000000000000000000)
  centralHi := (61194628765353260023/50000000000000000000)
  directionLo := (66097753527264203333/50000000000000000000)
  directionHi := (132195507054528406667/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree008.table
  base := (36601129146385990840108056294979932260813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-14454810573339712375968172783237485000000000000)
      constant := (118455694047233055379289380341633509949321461351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree008.table
  base := (3652866575518480442286104242849234826213/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-7235464336301481949345211973240367500000000000)
      constant := (59173980812835742822757544555879504764266235755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66097753527264203333/50000000000000000000)
  centralHi := (132195507054528406667/100000000000000000000)
  directionLo := (14132294156254368327/10000000000000000000)
  directionHi := (141322941562543683271/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree009.table
  base := (930054522900313701870851099104151412583/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-300971521929076938984830463328836250000000000)
      constant := (2035200997564845313287085912811218925106324528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree009.table
  base := (29701641580126429150042945638258789667971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-602614631327456024749754725126141250000000000)
      constant := (4068176073322906741357204441751522687918775371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14132294156254368327/10000000000000000000)
  centralHi := (141322941562543683271/100000000000000000000)
  directionLo := (18736951934269653551/12500000000000000000)
  directionHi := (149895615474157228409/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree010.table
  base := (6090305836139624269338336589294048274713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-9025056897500298517196758628138415000000000000)
      constant := (52875244282215264091773312548698208392111313302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree010.table
  base := (2431024035799592239002199335322444638571/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-9035130709539830718898165605165446250000000000)
      constant := (52866144488956442932462706056209180607314606085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18736951934269653551/12500000000000000000)
  centralHi := (149895615474157228409/100000000000000000000)
  directionLo := (79001926028519505721/50000000000000000000)
  directionHi := (158003852057039011443/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree011.table
  base := (156102036970515898365767801850985795499/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-9923882702915519681803094746398251250000000000)
      constant := (52497200639095187785892899853613155706060739072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree011.table
  base := (19937208506733435296336572413549856538443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-19869927792318010207349284842255971250000000000)
      constant := (105015388658031918428849869358364946707057751361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79001926028519505721/50000000000000000000)
  centralHi := (158003852057039011443/100000000000000000000)
  directionLo := (165715838082390115739/100000000000000000000)
  directionHi := (8285791904119505787/5000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree012.table
  base := (8180055992472426737415533027559059803177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-400841055864101512829978920913262500000000000)
      constant := (1981522840241035242374246497442852505463826977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree012.table
  base := (204026355206451707818916203127668208291/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96386233594244105879061956194635000000000000)
      linear := (-1203866342530908832050124359676725000000000000)
      constant := (5947855649203875802026569854632736421230842920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165715838082390115739/100000000000000000000)
  centralHi := (8285791904119505787/5000000000000000000)
  directionLo := (173084547888698618101/100000000000000000000)
  directionHi := (86542273944349309051/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree013.table
  base := (6662287701212859079829252284385835387757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5132994688450869543855370448235000000000000)
      linear := (-69358191205597408349205721792413750000000000)
      constant := (329451058023973517756885111970427496218333231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree013.table
  base := (6645765811817099562193781053706705864799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5132994688450869543855370448235000000000000)
      linear := (-69435682067439963746908852384929375000000000)
      constant := (329738905411524031653213084648705360335674117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173084547888698618101/100000000000000000000)
  centralHi := (86542273944349309051/50000000000000000000)
  directionLo := (180152109186435761701/100000000000000000000)
  directionHi := (90076054593217880851/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree014.table
  base := (2687994444419093396899347837462402196057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-12620360119161183175622103101177760000000000000)
      constant := (58877722430818659148969010843352536123903360278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree014.table
  base := (2144645023741279211476364402945778674163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-25268926912033056516008145738031207500000000000)
      constant := (117891336073432334828314219157187418467344259005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180152109186435761701/100000000000000000000)
  centralHi := (90076054593217880851/50000000000000000000)
  directionLo := (186952678961302235377/100000000000000000000)
  directionHi := (93476339480651117689/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree015.table
  base := (8552006377797488066168030929102770774217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-3004263538794756520050764270986132500000000000)
      constant := (13998577312055835095030965167618274648707322051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree015.table
  base := (8527004575349734051328625920266840065511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-1002540492047089084650411087776158750000000000)
      constant := (4672684090988197002966302983879755651509248911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186952678961302235377/100000000000000000000)
  centralHi := (93476339480651117689/50000000000000000000)
  directionLo := (193514407466973906891/100000000000000000000)
  directionHi := (48378601866743476723/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree016.table
  base := (6655822758591589654412538809407559864593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-28836023459983251009669550675394865000000000000)
      constant := (135883546357456790571022614849544332005270927411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree016.table
  base := (6634112724137973912299279347563571293983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-28868259658509754055114053001881365000000000000)
      constant := (136099185025454744779350588031921467605841102941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193514407466973906891/100000000000000000000)
  centralHi := (48378601866743476723/25000000000000000000)
  directionLo := (199860820632209637877/100000000000000000000)
  directionHi := (99930410316104818939/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree017.table
  base := (1001950418284520738543499513529513815579/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-30633675070813693338882222911914537500000000000)
      constant := (147314934757918012257779130171455845443338054165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree017.table
  base := (4990932073562581434356587334450461608543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-30667926031748102824667006633806443750000000000)
      constant := (147572056431077041329380680054745006854102024061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199860820632209637877/100000000000000000000)
  centralHi := (99930410316104818939/50000000000000000000)
  directionLo := (103005909236153219809/50000000000000000000)
  directionHi := (206011818472306439619/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree018.table
  base := (223206903026238404295601698863168634063/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-600580123734150660520275836082115000000000000)
      constant := (2966274299217144348513808363307511299930930104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree018.table
  base := (3555023938685789467877355243412419320561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-1202503422406905614600739269101167500000000000)
      constant := (5943653519629664187581738873738328855927473961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103005909236153219809/50000000000000000000)
  centralHi := (206011818472306439619/100000000000000000000)
  directionLo := (105992206171907762453/50000000000000000000)
  directionHi := (211984412343815524907/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree019.table
  base := (288317739334035909714915748993892697569/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-17114489146237288998653783692476941250000000000)
      constant := (87196607426329210735704419502485811223354546252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree019.table
  base := (573117786916358488970494976288076077487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-17133629389112400181886456948828300625000000000)
      constant := (87368540318535082323081246030578038264503175498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105992206171907762453/50000000000000000000)
  centralHi := (211984412343815524907/100000000000000000000)
  directionLo := (27224159997153457567/12500000000000000000)
  directionHi := (217793279977227660537/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree020.table
  base := (1188133441022463231856900203468108710977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-36026629903305020326520239621473555000000000000)
      constant := (189892213867207049315235406047414039445491478979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree020.table
  base := (73499711571046672910425522570909030067/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-18033462575731574566662933764790840000000000000)
      constant := (95140759059071371954230045627732777363056291272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27224159997153457567/12500000000000000000)
  centralHi := (217793279977227660537/100000000000000000000)
  directionLo := (111725595243128311219/50000000000000000000)
  directionHi := (223451190486256622439/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree021.table
  base := (48505472109091733899771048462639601413/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-700449657669175234365424293666541250000000000)
      constant := (3826343566679013233780135898484146339136847226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree021.table
  base := (36713049176213424030047522197947117559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-4207399058300166433653202351278528750000000000)
      constant := (23006530830272658506391317749810070639790882385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111725595243128311219/50000000000000000000)
  centralHi := (223451190486256622439/100000000000000000000)
  directionLo := (5724233368769328551/2500000000000000000)
  directionHi := (228969334750773142041/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree022.table
  base := (-693667579469505500622478365413976682323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-39621933124965904984945584094512900000000000000)
      constant := (224541084290354333354839519565776947531838319879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree022.table
  base := (-702665013861900892336734571058926560601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-39666257897939846672431774793431837500000000000)
      constant := (225025782161880028800288877803991173695754169973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5724233368769328551/2500000000000000000)
  centralHi := (228969334750773142041/100000000000000000000)
  directionLo := (187486068572911947/80000000000000000)
  directionHi := (234357585716139933751/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree023.table
  base := (-372361958097564379975199667727973197023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22815000000000000000000000000000000000000000
      center := (337662)
      previous := (168831)
      next := (168831)
      square := (1639841403304720137829031390835000000000000)
      linear := (-39148945875043806535121225265626250000000000)
      constant := (230257823610162932938224078688743500978968102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree023.table
  base := (-1497181698864108522213331402606535055869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45630000000000000000000000000000000000000000
      center := (675324)
      previous := (337662)
      next := (337662)
      square := (3279682806609440275658062781670000000000000)
      linear := (-78385490115648762650254685114096250000000000)
      constant := (461526587434465568740345971268259466477569753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187486068572911947/80000000000000000)
  centralHi := (234357585716139933751/100000000000000000000)
  directionLo := (14976544122860939917/6250000000000000000)
  directionHi := (239624705965775038673/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree024.table
  base := (-2205121990833767653013663515361720585679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-4801915149625198849263436507505805000000000000)
      constant := (29312126797477188088357805868708615453759135163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree024.table
  base := (-442352768011543371290579242716267998517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-1602429283126538674501395631751185000000000000)
      constant := (9792433063052326375833284382555339623322908415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14976544122860939917/6250000000000000000)
  centralHi := (239624705965775038673/100000000000000000000)
  directionLo := (244778515061413040091/100000000000000000000)
  directionHi := (61194628765353260023/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree025.table
  base := (-570060578141809362359960508980965255347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-45014887957457231972583600804071917500000000000)
      constant := (285106971960717522512286106997281217121657585155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree025.table
  base := (-2856002594109070193979373798464891552381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-45065257017654892981090635689207073750000000000)
      constant := (285747014617699155791817167496816893054728327913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244778515061413040091/100000000000000000000)
  centralHi := (61194628765353260023/25000000000000000000)
  directionLo := (249826025790262047347/100000000000000000000)
  directionHi := (62456506447565511837/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree026.table
  base := (-1716414632209887179581294096713521652231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5132994688450869543855370448235000000000000)
      linear := (-138498637775999036395846961658555000000000000)
      constant := (909725882798518035663667689400687332741184627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree026.table
  base := (-3437717325191110021486016994192986455529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10265989376901739087710740896470000000000000)
      linear := (-277307238999368294382506445687172500000000000)
      constant := (1823566011280046378500580898750030793205679293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249826025790262047347/100000000000000000000)
  centralHi := (62456506447565511837/25000000000000000000)
  directionLo := (995209203521781643/390625000000000000)
  directionHi := (254773556101576100609/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree027.table
  base := (-197955024448728636999054244850686810409/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-900188725539224382055721208835393750000000000)
      constant := (6128422656737644839464182803856818812751249910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree027.table
  base := (-1981645110182302706955652282529678105213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-901196106743177602225861906538096875000000000)
      constant := (6142355760608380067370188298604264032872102587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (995209203521781643/390625000000000000)
  centralHi := (254773556101576100609/100000000000000000000)
  directionLo := (16226676364565495447/6250000000000000000)
  directionHi := (259626821833047927153/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree028.table
  base := (-4434346571522265642939026144300891031117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-50407842789948558960221617513630935000000000000)
      constant := (355436772862052674704540293814115173105031945241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree028.table
  base := (-443793611796680081677639063602331902727/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-25232128068684969644874748292491155000000000000)
      constant := (178124046199847068528897082653226939013680968855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16226676364565495447/6250000000000000000)
  centralHi := (259626821833047927153/100000000000000000000)
  directionLo := (66097753527264203333/25000000000000000000)
  directionHi := (264391014109056813333/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree029.table
  base := (-2431423169464342063959158390397153064173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-26102747200389500644717144875075303750000000000)
      constant := (190491434116370793892480693753730232694941479929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree029.table
  base := (-4865920526080525899354003448666288039131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-52263922510608288059302450216907388750000000000)
      constant := (381855003688273625733918581641034327089806035663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66097753527264203333/25000000000000000000)
  centralHi := (264391014109056813333/100000000000000000000)
  directionLo := (67267716099599807413/25000000000000000000)
  directionHi := (269070864398399229653/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree030.table
  base := (-1049620809188228715971999803750601324371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-2000116518948497911801739332839640000000000000)
      constant := (15094987070784281945134928569933834329999541145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree030.table
  base := (-1312684013709828542318950569146072598453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96386233594244105879061956194635000000000000)
      linear := (-3003532715769257601603077991601803750000000000)
      constant := (22694417465663899604457633995498062641129220082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67267716099599807413/25000000000000000000)
  centralHi := (269070864398399229653/100000000000000000000)
  directionLo := (68417674888596958381/25000000000000000000)
  directionHi := (10946827982175513341/4000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree031.table
  base := (-5592992515003476359695960580777657317983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-55800797622439885947859634223189952500000000000)
      constant := (435175186400973620369294209710592362737855049059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree031.table
  base := (-559524538275034252438661327912646950209/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-27931627628542492799204178740378773125000000000)
      constant := (218087357235025447603478286473251507293558050785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68417674888596958381/25000000000000000000)
  centralHi := (10946827982175513341/4000000000000000000)
  directionLo := (69548622165123749599/25000000000000000000)
  directionHi := (278194488660494998397/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree032.table
  base := (-2949934643135633274207282591199648119579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-28799224616635164138536153229854812500000000000)
      constant := (231904392004027239140727451726113916978460981167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree032.table
  base := (-295089862030046523714143143950892998301/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-28831460815161667183980655556341312500000000000)
      constant := (232437467261392784812092725760480443065900920730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69548622165123749599/25000000000000000000)
  centralHi := (278194488660494998397/100000000000000000000)
  directionLo := (282645883125087366541/100000000000000000000)
  directionHi := (141322941562543683271/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree033.table
  base := (-6170670969648961944167675626665490092613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-6599566760455641178476108744025477500000000000)
      constant := (54828974343460262526650626230980893529440915561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree033.table
  base := (-3086160303995689724458681256117302232377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-1101159037102994132176190087863105625000000000)
      constant := (9159176265131714061706765605042051067029513823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282645883125087366541/100000000000000000000)
  centralHi := (141322941562543683271/50000000000000000000)
  directionLo := (287028251177557109919/100000000000000000000)
  directionHi := (1793926569859731937/625000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree034.table
  base := (-1601747492448544407998177825922927964437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-30596876227465606467748825466374485000000000000)
      constant := (262063648930439898348312894328104362183273859202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree034.table
  base := (-320420064762717268015146998591687793299/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-30631127188400015953533609188266391250000000000)
      constant := (262666318990617010254385029163600551149019547270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287028251177557109919/100000000000000000000)
  centralHi := (1793926569859731937/625000000000000000)
  directionLo := (145672353846339938897/50000000000000000000)
  directionHi := (58268941538535975559/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree035.table
  base := (-51641694851274313482137737174390925417/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-31495702032880827632355161584634321250000000000)
      constant := (277902603312317751630868608883737669052476385024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree035.table
  base := (-6611344268410033019676458794604384711831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-63061920750038380676620172008457861250000000000)
      constant := (557083143552936300235106153885334968387632612763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145672353846339938897/50000000000000000000)
  centralHi := (58268941538535975559/20000000000000000000)
  directionLo := (7389953502349462883/2500000000000000000)
  directionHi := (295598140093978515321/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree036.table
  base := (-1356238335443891098824480848743089232829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-2399594654688596207182333163177345000000000000)
      constant := (21795995886901633615833629827250500397479272855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree036.table
  base := (-6782224422723220008536400287933550758759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-2402281004565804794302708357051220000000000000)
      constant := (21846090385963226156887329433626154503616186641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7389953502349462883/2500000000000000000)
  centralHi := (295598140093978515321/100000000000000000000)
  directionLo := (18736951934269653551/6250000000000000000)
  directionHi := (299791230948314456817/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree037.table
  base := (-3460522310578703122208046335216038504299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-33293353643711269961567833821153993750000000000)
      constant := (311092597725814891696953097155555493159658457727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree037.table
  base := (-6921927987566861056479148897973255827463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-66661253496515078215726079272308018750000000000)
      constant := (623614389381057807315247828916412963829199969099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18736951934269653551/6250000000000000000)
  centralHi := (299791230948314456817/100000000000000000000)
  directionLo := (7598161943851613301/2500000000000000000)
  directionHi := (303926477754064532041/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree038.table
  base := (-1406086150928722696989970142716797400027/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-68384358898252982252348339878827660000000000000)
      constant := (656883352021418302543658185784025256036425133355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree038.table
  base := (-11249898120551131142021142894975539683/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-68460919869753426985279032904233097500000000000)
      constant := (658391225050772048346790358854318970452251974375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7598161943851613301/2500000000000000000)
  centralHi := (303926477754064532041/100000000000000000000)
  directionLo := (308006210337516003113/100000000000000000000)
  directionHi := (154003105168758001557/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree039.table
  base := (-1777489324378250081914733866125639448387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (190110914387069242365013720305000000000000)
      linear := (-7690336457274098683055118574988750000000000)
      constant := (75891397428454656161105701724250401588606554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree039.table
  base := (-7110603549480085926999447807480728271753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (234876)
      previous := (117438)
      next := (117438)
      square := (1140665486322415454190082321830000000000000)
      linear := (-46193679318206295696799465178276250000000000)
      constant := (456392826564665172208740896249816170170227989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308006210337516003113/100000000000000000000)
  centralHi := (154003105168758001557/50000000000000000000)
  directionLo := (62406521240320523761/20000000000000000000)
  directionHi := (156016303100801309403/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree040.table
  base := (-57281010946431760839597357681293153303/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-71979662119913866910773684351867005000000000000)
      constant := (729288606156321253641031181851649973955259927375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree040.table
  base := (-358033955727826131057511081746241189493/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-36030126308115062262192470084041627500000000000)
      constant := (365479988123175833909010531919078258682896802890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62406521240320523761/20000000000000000000)
  centralHi := (156016303100801309403/50000000000000000000)
  directionLo := (79001926028519505721/25000000000000000000)
  directionHi := (63201540822815604577/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree041.table
  base := (-7181353541976921520046335056246897926097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-73777313730744309239986356588386677500000000000)
      constant := (766993488568090552767392071537040303338493056781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree041.table
  base := (-1436365262505200886191473204361106805349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-73859918989468473293937893800008333750000000000)
      constant := (768749688559986677702669622942013073802761696885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79001926028519505721/25000000000000000000)
  centralHi := (63201540822815604577/20000000000000000000)
  directionLo := (319933416175830172213/100000000000000000000)
  directionHi := (159966708087915086107/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree042.table
  base := (-7173983062742666726676971770755637623509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-8397218371286083507688780980545150000000000000)
      constant := (89522078802379381937415156526188998847462015673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree042.table
  base := (-1793596858032310602898314613592582499051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-1401103432642718927101682359850618750000000000)
      constant := (14954477776295493189616055668093403517129683098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319933416175830172213/100000000000000000000)
  centralHi := (159966708087915086107/50000000000000000000)
  directionLo := (323811538572088592581/100000000000000000000)
  directionHi := (161905769286044296291/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree043.table
  base := (-7138300327331478245914156980771845805577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-77372616952405193898411701061426022500000000000)
      constant := (845403579217959664120341137818694284473411486821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree043.table
  base := (-7138646195917374130641657329995930310687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-77459251735945170833043801063858491250000000000)
      constant := (847335625469107086686465212462184013174382830851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323811538572088592581/100000000000000000000)
  centralHi := (161905769286044296291/50000000000000000000)
  directionLo := (163821880589032951609/50000000000000000000)
  directionHi := (327643761178065903219/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree044.table
  base := (-7074542138610331024668587314738607522721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-79170268563235636227624373297945695000000000000)
      constant := (886107526956572251283029652675475301219252936733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree044.table
  base := (-707483797391850235597452685993304118487/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-39629459054591759801298377347891785000000000000)
      constant := (444065298532454607912200081170641542560424401255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163821880589032951609/50000000000000000000)
  centralHi := (327643761178065903219/100000000000000000000)
  directionLo := (331431676164780231479/100000000000000000000)
  directionHi := (8285791904119505787/2500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree045.table
  base := (-6982905136075100481054610166392373985817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-2998811858298743650253223908683902500000000000)
      constant := (34363336214204732905626713054802346779543974383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree045.table
  base := (-3491579089843453411282454530842200668159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-1501084897822627192076846450513123125000000000)
      constant := (17220856352089806171541501530006637453222167241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331431676164780231479/100000000000000000000)
  centralHi := (8285791904119505787/2500000000000000000)
  directionLo := (167588392864692466829/50000000000000000000)
  directionHi := (335176785729384933659/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree046.table
  base := (-3431776367064275230940878354330025221341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22815000000000000000000000000000000000000000
      center := (337662)
      previous := (168831)
      next := (168831)
      square := (1639841403304720137829031390835000000000000)
      linear := (-78228328719183857170179317363880000000000000)
      constant := (917307029531879674271231783581007407415021017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree046.table
  base := (-3431884589468022692160618745569940527563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22815000000000000000000000000000000000000000
      center := (337662)
      previous := (168831)
      next := (168831)
      square := (1639841403304720137829031390835000000000000)
      linear := (-78315927084745006750191551946723750000000000)
      constant := (919397137419834612638810719144137095747730031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167588392864692466829/50000000000000000000)
  centralHi := (335176785729384933659/100000000000000000000)
  directionLo := (169440254528232079449/50000000000000000000)
  directionHi := (338880509056464158899/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree047.table
  base := (-1679155209442101637437305789387242533937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-42281611697863481607631195003752356250000000000)
      constant := (507104738644511013557143453159053195016443906202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree047.table
  base := (-3358402989873509180190954787563280947983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-42328958614449282955627807795779403125000000000)
      constant := (508259028155382149205108628299046612907141789059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169440254528232079449/50000000000000000000)
  centralHi := (338880509056464158899/100000000000000000000)
  directionLo := (17127209430089199/5000000000000000)
  directionHi := (342544188601783980001/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree048.table
  base := (-3271111277795608918969353080868726352377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-1599275463084396398971760411926377500000000000)
      constant := (19609365275774509284253766895768069995371143823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree048.table
  base := (-3271190461849294379329148554958504907407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96386233594244105879061956194635000000000000)
      linear := (-4803199089007606371156031623526882500000000000)
      constant := (58961868144525073733511663722348096608318720379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17127209430089199/5000000000000000)
  centralHi := (342544188601783980001/100000000000000000000)
  directionLo := (346169095777397236203/100000000000000000000)
  directionHi := (86542273944349309051/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree049.table
  base := (-6340452089645702376329114140300968759/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-44079263308693923936843867240272028750000000000)
      constant := (552299676332842233570513844658161160101059653500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree049.table
  base := (-6340587556960494484235314361495475127227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-88257249975375263450361522855408963750000000000)
      constant := (1107108656457975846612622408719096621721008532271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346169095777397236203/100000000000000000000)
  centralHi := (86542273944349309051/25000000000000000000)
  directionLo := (174878218053183433143/50000000000000000000)
  directionHi := (349756436106366866287/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree050.table
  base := (-6111387948855562851395569163284742223263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-89956178228218290202900406717063730000000000000)
      constant := (1151290171103645150003673552671674958658447742499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree050.table
  base := (-763937978454969475275039796894711598073/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-45028458174306806109957238243667021250000000000)
      constant := (576951478863546266116519810977005403058807978516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174878218053183433143/50000000000000000000)
  centralHi := (349756436106366866287/100000000000000000000)
  directionLo := (22081709619147450511/6250000000000000000)
  directionHi := (353307353906359208177/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree051.table
  base := (-5855095606035590804353347472202856248557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-10194869982116525836901453217064822500000000000)
      constant := (133219780240628604457342661759256497814318266929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree051.table
  base := (-5855194729029044554008561485275873592051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-3402095656364887444054349263676263750000000000)
      constant := (44507273093564322735978414049277319320309548549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22081709619147450511/6250000000000000000)
  centralHi := (353307353906359208177/100000000000000000000)
  directionLo := (356822936553691321619/100000000000000000000)
  directionHi := (17841146827684566081/5000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree052.table
  base := (-348226856049035253330349802839512605089/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5132994688450869543855370448235000000000000)
      linear := (-276779530916802292489129441390837500000000000)
      constant := (3691309982162242149153753575292268431692110504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree052.table
  base := (-1114342897343075901693311959673440468797/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10265989376901739087710740896470000000000000)
      linear := (-554178988728345028159883927521800000000000000)
      constant := (7399341851859303874402977245530656873920862245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356822936553691321619/100000000000000000000)
  centralHi := (17841146827684566081/5000000000000000000)
  directionLo := (180152109186435761701/50000000000000000000)
  directionHi := (360304218372871523403/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree053.table
  base := (-5261035840816558772123785074992423415171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-95349133060709617190538423426622747500000000000)
      constant := (1297344316401088799548635337412102304033778030583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree053.table
  base := (-5261108369829328039093659089111842892001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-95455915468328658528573337383109278750000000000)
      constant := (1300280046769199824889577465593332080380967402173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180152109186435761701/50000000000000000000)
  centralHi := (360304218372871523403/100000000000000000000)
  directionLo := (2910017473528538457/800000000000000000)
  directionHi := (181876092095533653563/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree054.table
  base := (-984670430366352926265046944060677467561/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-3598029061908891093324114654190460000000000000)
      constant := (49926761387278952288459735377096978743612895195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree054.table
  base := (-1538566935091519008576844203021931027/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-1801029293362351987002338722500636250000000000)
      constant := (25019816734535246212842439559467548228933276800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2910017473528538457/800000000000000000)
  centralHi := (181876092095533653563/50000000000000000000)
  directionLo := (45895971574014945017/12500000000000000000)
  directionHi := (367167772592119560137/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree055.table
  base := (-284913155638547541487937247606487825747/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-49472218141185250924481883949831046250000000000)
      constant := (699848710115852614113006098635839322222699769848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree055.table
  base := (-2279331779073270236624377776752955904593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-49527624107402678033839622323479718125000000000)
      constant := (701429433682323173743719218738383360188152742589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45895971574014945017/12500000000000000000)
  centralHi := (367167772592119560137/100000000000000000000)
  directionLo := (46318984862571586729/12500000000000000000)
  directionHi := (370551878900572693833/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree056.table
  base := (-4166837503207416204172742329319458535607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-100742087893200944178176440136181765000000000000)
      constant := (1452368840404791932093094982216080034361371362011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree056.table
  base := (-2083441447704621052690451341205840252881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-50427457294021852418616099139442257500000000000)
      constant := (727823137037881731787850864393751872739909014413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46318984862571586729/12500000000000000000)
  centralHi := (370551878900572693833/100000000000000000000)
  directionLo := (74781071584520894151/20000000000000000000)
  directionHi := (93476339480651117689/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree057.table
  base := (-374805548924426483222322313658301068547/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-1898884064889470120507205784679656250000000000)
      constant := (27889569706503963065561694568552358708979148265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree057.table
  base := (-3748094315045715570134682956225319737633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-11406064551253561511865016878978843750000000000)
      constant := (167714696714023437170117256629890097718845116501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74781071584520894151/20000000000000000000)
  centralHi := (93476339480651117689/25000000000000000000)
  directionLo := (94307256616907940679/25000000000000000000)
  directionHi := (377229026467631762717/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree058.table
  base := (-412785389596935632073269447586779640447/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-52168695557430914418300892304610555000000000000)
      constant := (780350573204283593591388227004977754905854957324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree058.table
  base := (-3302316325164578194700635735017748438791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-104454247334520402376338105542734672500000000000)
      constant := (1564216811740616460916458822069386216307988436843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94307256616907940679/25000000000000000000)
  centralHi := (377229026467631762717/100000000000000000000)
  directionLo := (95130916417917042237/25000000000000000000)
  directionHi := (380523665671668168949/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree059.table
  base := (-44211500350827736297325241639361089689/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-53067521362846135582907228422870391250000000000)
      constant := (808180974716339467716772069045047180906071646304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree059.table
  base := (-353695553159832048196636781994401960749/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-53126956853879375572945529587329875625000000000)
      constant := (809999930302918747752801634536880230242383244308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95130916417917042237/25000000000000000000)
  centralHi := (380523665671668168949/100000000000000000000)
  directionLo := (383790023141156913503/100000000000000000000)
  directionHi := (11993438223161153547/3125000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree060.table
  base := (-291228413663556890748490554524472913373/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96386233594244105879061956194635000000000000)
      linear := (-5996260796473484083057062726792247500000000000)
      constant := (92945507866394305692902258357743341164858485124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree060.table
  base := (-2329851601117377644565190367403632449433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-4001984447444337033905333807651290000000000000)
      constant := (62103014284317397462965539410073632230388240367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383790023141156913503/100000000000000000000)
  centralHi := (11993438223161153547/3125000000000000000)
  directionLo := (387028814933947813783/100000000000000000000)
  directionHi := (48378601866743476723/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree061.table
  base := (-1803167961915165899904890559358771749663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-109730345947353155824239801318780127500000000000)
      constant := (1730672696380963416095188790352897547032576209699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree061.table
  base := (-90159436845679627309257050085293953201/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-54926623227117724342498483219254954375000000000)
      constant := (867280680340079019948072130655461313852485647730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387028814933947813783/100000000000000000000)
  centralHi := (48378601866743476723/12500000000000000000)
  directionLo := (195120363696144163751/50000000000000000000)
  directionHi := (390240727392288327503/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree062.table
  base := (-1249567192595092199721681627250794483963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-111527997558183598153452473555299800000000000000)
      constant := (1789322591553325136807321252539152417128159043599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree062.table
  base := (-1249584959153615159483206353002380189353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-111652912827473797454549920070434987500000000000)
      constant := (1793339763586843340663473978376922734103424616069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195120363696144163751/50000000000000000000)
  centralHi := (390240727392288327503/100000000000000000000)
  directionLo := (393426418841120226689/100000000000000000000)
  directionHi := (39342641884112022669/10000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree063.table
  base := (-334516365153260374881385100966589866889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-2098623132759519268197502699848508750000000000)
      constant := (34240163119552119819254112377168184102435256511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree063.table
  base := (-669047923364483424257411439247771203063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-4201947377804153563855661988976298750000000000)
      constant := (68633947256203991496035180293887926139487464737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393426418841120226689/100000000000000000000)
  centralHi := (39342641884112022669/10000000000000000000)
  directionLo := (198293260581792609999/50000000000000000000)
  directionHi := (396586521163585219999/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree064.table
  base := (-30785530924128023708394301542290473457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-57561650389922241405938909014169572500000000000)
      constant := (954805665715210659264436563825186577613326710061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree064.table
  base := (-61584053522799318787356605604175176161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-115252245573950494993655827334285145000000000000)
      constant := (1913891782165783159861147217122714790647052821853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198293260581792609999/50000000000000000000)
  centralHi := (396586521163585219999/100000000000000000000)
  directionLo := (79944328252883855151/20000000000000000000)
  directionHi := (99930410316104818939/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree065.table
  base := (286406183315825545503431188657558312719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5132994688450869543855370448235000000000000)
      linear := (-345919977487203920535770681256978750000000000)
      constant := (5832101027606764705967440113619892389755565477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree065.table
  base := (572801257971390080173826934869166295539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10265989376901739087710740896470000000000000)
      linear := (-692614863592833395048572668439113750000000000)
      constant := (11690327629084903435697800269133254075636683537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79944328252883855151/20000000000000000000)
  centralHi := (99930410316104818939/25000000000000000000)
  directionLo := (80566472486166939493/20000000000000000000)
  directionHi := (201416181215417348733/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree066.table
  base := (154264122649477896203751606230361234727/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-2198492666694543842042651157432935000000000000)
      constant := (37664541576242896081395256396978834286483314108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree066.table
  base := (617051741583376517429438683772836154221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96386233594244105879061956194635000000000000)
      linear := (-6602865462245955140708985255451961250000000000)
      constant := (113246518135361841859650745374065267459445534863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80566472486166939493/20000000000000000000)
  centralHi := (201416181215417348733/50000000000000000000)
  directionLo := (405919245599532554257/100000000000000000000)
  directionHi := (202959622799766277129/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree067.table
  base := (384465387848799929902206331894335740763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-120516255612335809799515834737898162500000000000)
      constant := (2097516615513138812767988528044327923009343650005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree067.table
  base := (961159409404570290125968542378728035351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-60325622346832770651157344115030190625000000000)
      constant := (1051103822174439512874862699175067632469105948277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405919245599532554257/100000000000000000000)
  centralHi := (202959622799766277129/50000000000000000000)
  directionLo := (408982830537639924553/100000000000000000000)
  directionHi := (204491415268819962277/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree068.table
  base := (164840688227134593733340410931532415349/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-61156953611583126064364253487208917500000000000)
      constant := (1081072125362281766026486395404640692264357044984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree068.table
  base := (2637444069422173583237813409190561635651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-122450911066903890071867641861985460000000000000)
      constant := (2166976315339119135647214144139698576446298546377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408982830537639924553/100000000000000000000)
  centralHi := (204491415268819962277/50000000000000000000)
  directionLo := (103005909236153219809/25000000000000000000)
  directionHi := (412023636944612879237/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree069.table
  base := (3379482483996550632539443321926529328051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (75036)
      previous := (37518)
      next := (37518)
      square := (364409200734382252850895864630000000000000)
      linear := (-26068380347405312845608313213807500000000000)
      constant := (467920215122741355624122338201140969119321857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree069.table
  base := (52804321085028855214083705717333311049/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (60734866789063708808482644105000000000000)
      linear := (-4349596633765393784268731901348125000000000)
      constant := (78160867217137386295612978152852248702402992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103005909236153219809/25000000000000000000)
  centralHi := (412023636944612879237/100000000000000000000)
  directionLo := (83008433096295084861/20000000000000000000)
  directionHi := (207521082740737712153/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree070.table
  base := (2074209537038554142797230360933566236763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-62954605222413568393576925723728590000000000000)
      constant := (1147194145214298236578225882668576682701086922001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree070.table
  base := (4148414001261686178879758017147743117889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-126050243813380587610973549125835617500000000000)
      constant := (2299508691656289887608931071484992797045774651203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83008433096295084861/20000000000000000000)
  centralHi := (207521082740737712153/50000000000000000000)
  directionLo := (418038898733166573407/100000000000000000000)
  directionHi := (13063715585411455419/3125000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree071.table
  base := (2472129431237769061374339196546790366863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-63853431027828789558183261841988426250000000000)
      constant := (1181002342389568964674702608905754794585248814701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree071.table
  base := (988850905314236891461207440493664800203/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-127849910186618936380526502757760696250000000000)
      constant := (2367272386951555910418375903911174458329335534405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418038898733166573407/100000000000000000000)
  centralHi := (13063715585411455419/3125000000000000000)
  directionLo := (210507151054616767167/50000000000000000000)
  directionHi := (84202860421846706867/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree072.table
  base := (720875029322861853688411730261653239447/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-2398231734564592989732948072601787500000000000)
      constant := (45011431913955727704882514147781345745039204988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree072.table
  base := (5766996528806859053988356089962999622053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-4801836168883603153706646532951325000000000000)
      constant := (90223496850248763112596282456428872129211160253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210507151054616767167/50000000000000000000)
  centralHi := (84202860421846706867/20000000000000000000)
  directionLo := (105992206171907762453/25000000000000000000)
  directionHi := (423968824687631049813/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree073.table
  base := (6616641831887885752610206285927143161791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-131302165277318463774791868157016197500000000000)
      constant := (2500226202872799335287862534550623492415546484157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree073.table
  base := (6616638664897870836122392238487465738093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-131449242933095633919632410021610853750000000000)
      constant := (2505794772429831314062682579497068032046121311911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105992206171907762453/25000000000000000000)
  centralHi := (423968824687631049813/100000000000000000000)
  directionLo := (5336286250074482667/1250000000000000000)
  directionHi := (426902900005958613361/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree074.table
  base := (1873295627781117335351397013492053111403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-66549908444074453052002270196767935000000000000)
      constant := (1285415660288530803871970140146047603233977138562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree074.table
  base := (7493179804789479697503162050053008182003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-133248909306333982689185363653535932500000000000)
      constant := (2576553456643143397339784306488257608049689755481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5336286250074482667/1250000000000000000)
  centralHi := (426902900005958613361/100000000000000000000)
  directionLo := (107454236701020706471/25000000000000000000)
  directionHi := (85963389360816565177/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree075.table
  base := (8396621309985458145863043122921349746543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-4996202536999235127156193060372427500000000000)
      constant := (97867876820131594150775721498625389244940690743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree075.table
  base := (8396618997478239314571232161262196838663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-15005397297730259050970924142829001250000000000)
      constant := (294256718366788339782505145659986527439657432589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107454236701020706471/25000000000000000000)
  centralHi := (85963389360816565177/20000000000000000000)
  directionLo := (432711369721746545253/100000000000000000000)
  directionHi := (216355684860873272627/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree076.table
  base := (9326957418336770820043731582015063188113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-136695120109809790762429884866575215000000000000)
      constant := (2715030261616750119095851622937696583930173238451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree076.table
  base := (18216709848635598908002692520290701049/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-68424121026405340114145635458693045000000000000)
      constant := (1360532898235753881393987739183758359024997157888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432711369721746545253/100000000000000000000)
  centralHi := (216355684860873272627/50000000000000000000)
  directionLo := (27224159997153457567/6250000000000000000)
  directionHi := (435586559954455321073/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree077.table
  base := (160690471156903904368243177722426043563/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-69246385860320116545821278551547443750000000000)
      constant := (1394312040675046599337906484037238144646952459232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree077.table
  base := (2056837693199386806832234699416016205453/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-138647908426049028997844224549311168750000000000)
      constant := (2794819448527794961872132417543405734144237493155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27224159997153457567/6250000000000000000)
  centralHi := (435586559954455321073/100000000000000000000)
  directionLo := (438442895870651058569/100000000000000000000)
  directionHi := (43844289587065105857/10000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree078.table
  base := (1408539867831441215007766924044931221947/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (570332743161207727095041160915000000000000)
      linear := (-46117824895289505398045769013680000000000000)
      constant := (941227525298146408529757755160462535896919556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree078.table
  base := (2817079375148661494231493811909302164309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (190110914387069242365013720305000000000000)
      linear := (-15389828489950402998838174247341250000000000)
      constant := (314439121203202208137838000433702619814838922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438442895870651058569/100000000000000000000)
  centralHi := (43844289587065105857/10000000000000000000)
  directionLo := (55160092949116193761/12500000000000000000)
  directionHi := (441280743592929550089/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree079.table
  base := (6139671650168112561741437669226262616421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-71044037471150558875033950788067116250000000000)
      constant := (1469400206134736865556432558246220530796982653167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree079.table
  base := (1534917758565134541106462915004804643321/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-71123620586262863268475065906580663125000000000)
      constant := (1472660855018065195419814163056628051229063147868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55160092949116193761/12500000000000000000)
  centralHi := (441280743592929550089/100000000000000000000)
  directionLo := (2775627859661434313/625000000000000000)
  directionHi := (444100457545829490081/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree080.table
  base := (6658631409769394455473251678153730598107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-71942863276565780039640286906326952500000000000)
      constant := (1507691460651928910934238376595974860068436825489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree080.table
  base := (1664657720924976234823389116185350696283/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-72023453772882037653251542722543202500000000000)
      constant := (1511035158681824512396459139432050983560626820164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2775627859661434313/625000000000000000)
  centralHi := (444100457545829490081/100000000000000000000)
  directionLo := (446902380972513244877/100000000000000000000)
  directionHi := (223451190486256622439/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree081.table
  base := (287641543138222688736960760581338056039/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-2697840336369666711268393445355066250000000000)
      constant := (57277067745024643797608467885521193916823565975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree081.table
  base := (719103812915721589889568739694613853413/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-2700862479981526371778815538463175625000000000)
      constant := (57404022986386919638332036875685872609996006130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446902380972513244877/100000000000000000000)
  centralHi := (223451190486256622439/50000000000000000000)
  directionLo := (17987473856898867409/4000000000000000000)
  directionHi := (224843423211235842613/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree082.table
  base := (1547378602316853349632414466048468319433/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-73740514887396222368852959142846625000000000000)
      constant := (1585768311176804636545723002885594759752960000455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree082.table
  base := (483555789242841391962565056174812147601/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-73823120146120386422804496354468281250000000000)
      constant := (1589281240525365564992648733100629142118291464432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17987473856898867409/4000000000000000000)
  centralHi := (224843423211235842613/50000000000000000000)
  directionLo := (452454176212214779673/100000000000000000000)
  directionHi := (226227088106107389837/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree083.table
  base := (16592389174554705911812041638107016865251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-149278681385622887066918590522212922500000000000)
      constant := (3251107813082307855418077136599840380417548225577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree083.table
  base := (16592388519255273871825079826212669123979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-149445906665479121615161946340861641250000000000)
      constant := (3258306036140602211883793445963325338746964357633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452454176212214779673/100000000000000000000)
  centralHi := (226227088106107389837/50000000000000000000)
  directionLo := (455204682860754596713/100000000000000000000)
  directionHi := (227602341430377298357/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree084.table
  base := (17737886405660342847232590941338017978949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-5595419740609382570227083805878985000000000000)
      constant := (123395378885985332456699417067157635145336019549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree084.table
  base := (1108617865383198263324769228007899873651/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96386233594244105879061956194635000000000000)
      linear := (-8402531835484303910261938887377040000000000000)
      constant := (185502661446965439764923932480149779971002553224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455204682860754596713/100000000000000000000)
  centralHi := (227602341430377298357/50000000000000000000)
  directionLo := (5724233368769328551/1250000000000000000)
  directionHi := (457938669501546284081/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree085.table
  base := (9455138771689577649345334241644374904259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-76436992303641885862671967497626133750000000000)
      constant := (1706619436226824500781231111361076981776397789193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree085.table
  base := (9455138532831916386428954992538442847867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-76522619705977909577133926802355899375000000000)
      constant := (1710394045176467001718534595803309007020857007009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5724233368769328551/1250000000000000000)
  centralHi := (457938669501546284081/100000000000000000000)
  directionLo := (115164107568106018793/25000000000000000000)
  directionHi := (460656430272424075173/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree086.table
  base := (10054781220910123003170726553373346496837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-77335818109057107027278303615885970000000000000)
      constant := (1747899370163143772126385788603541500166920565199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree086.table
  base := (20109562033990357274381828944441673166481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-154844905785194167923820807236636877500000000000)
      constant := (3503526588716010326731213157156316069833177332787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115164107568106018793/25000000000000000000)
  centralHi := (460656430272424075173/100000000000000000000)
  directionLo := (463358250684952162327/100000000000000000000)
  directionHi := (57919781335619020291/12500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree087.table
  base := (21335740978024677429305772843395254553123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-17385476425438295153752142163143512500000000000)
      constant := (397706092582524222341591619470364169175661247969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree087.table
  base := (2666967578735742181713088212209637883657/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-2900825410341342901729143719788184375000000000)
      constant := (66430803719296132785063766963717836224653527828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463358250684952162327/100000000000000000000)
  centralHi := (57919781335619020291/12500000000000000000)
  directionLo := (233022203987251630167/50000000000000000000)
  directionHi := (93208881594900652067/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree088.table
  base := (22588813048358475178836695324520940740183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-158266939439775098712981951704811285000000000000)
      constant := (3663907150952785886530255375281962943824053710341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree088.table
  base := (22588812751199334304315164543349359873059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-158444238531670865462926714500487035000000000000)
      constant := (3671998526484301115626389633784694390294306386793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233022203987251630167/50000000000000000000)
  centralHi := (93208881594900652067/20000000000000000000)
  directionLo := (468715171432279867501/100000000000000000000)
  directionHi := (234357585716139933751/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree089.table
  base := (596719464136868405353701281473188884787/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-80032295525302770521097311970665478750000000000)
      constant := (1874727846622825443847166110345739511733349996980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree089.table
  base := (23868778311851335407009352225590982701437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-160243904904909214232479668132412113750000000000)
      constant := (3757731965435159835353842230895058986837199069399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468715171432279867501/100000000000000000000)
  centralHi := (234357585716139933751/50000000000000000000)
  directionLo := (471370802720403729847/100000000000000000000)
  directionHi := (58921350340050466231/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree090.table
  base := (5035127491150929412561683427561034217791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-5994897876349480865607677636216690000000000000)
      constant := (142074091109022589811068014286956504475523665955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree090.table
  base := (12587818619653439061005237904138373867797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-3000806875521251166704307810450688750000000000)
      constant := (71193772546657041424615124270541270465279919597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471370802720403729847/100000000000000000000)
  centralHi := (58921350340050466231/12500000000000000000)
  directionLo := (237005778085558517163/50000000000000000000)
  directionHi := (474011556171117034327/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree091.table
  base := (5301877931430319175642840654950764525733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10265989376901739087710740896470000000000000)
      linear := (-968401741256014353258106321978522500000000000)
      constant := (23216221602940196516035007499225141817355222195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree091.table
  base := (26509389472445777883843187137675251903881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10265989376901739087710740896470000000000000)
      linear := (-969486613321810128825950150273741250000000000)
      constant := (23267418831891886204753759820824415583880632323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237005778085558517163/50000000000000000000)
  centralHi := (474011556171117034327/100000000000000000000)
  directionLo := (476637679071063691051/100000000000000000000)
  directionHi := (119159419767765922763/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree092.table
  base := (13935017558687315674218558813667114884911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22815000000000000000000000000000000000000000
      center := (337662)
      previous := (168831)
      next := (168831)
      square := (1639841403304720137829031390835000000000000)
      linear := (-156387094407463958440295501560387500000000000)
      constant := (3792134844970963550562527346086223045219848893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree092.table
  base := (27870034959768961277059416001252553791351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45630000000000000000000000000000000000000000
      center := (675324)
      previous := (337662)
      next := (337662)
      square := (3279682806609440275658062781670000000000000)
      linear := (-313124582277172515200639941452150000000000000)
      constant := (7600987070929292205087254365308963527949934613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476637679071063691051/100000000000000000000)
  centralHi := (119159419767765922763/25000000000000000000)
  directionLo := (95849882386310015469/20000000000000000000)
  directionHi := (239624705965775038673/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree093.table
  base := (2925757379235765570376046012679621249511/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-3097318472109765006648987275692771250000000000)
      constant := (75955779723785197484691989391509252299762664555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree093.table
  base := (29257573657887144713534120194891230138801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-18604730044206956590076831406679158750000000000)
      constant := (456738761245594048484095561438681875057854344603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95849882386310015469/20000000000000000000)
  centralHi := (239624705965775038673/50000000000000000000)
  directionLo := (60230873593202654847/12500000000000000000)
  directionHi := (481846988745621238777/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree094.table
  base := (3834000705621156415612416599676074009323/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-84526424552378876344128992561964660000000000000)
      constant := (2096070884061314037923425572444905315103308436484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree094.table
  base := (30672005530247332105101553290276560020297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-169242236771100958080244436292037507500000000000)
      constant := (4201373854567748739311984031614592103512863446619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60230873593202654847/12500000000000000000)
  centralHi := (481846988745621238777/100000000000000000000)
  directionLo := (242215318616365131337/50000000000000000000)
  directionHi := (19377225489309210507/4000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree095.table
  base := (32113330643925192536006789907545906926813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-170850500715588195017470657360448992500000000000)
      constant := (4283667655018446962905152479929624706848178243351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree095.table
  base := (32113330546059588798545249457141395896621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-171041903144339306849797389923962586250000000000)
      constant := (4293097170519480909762359953182131132318890478567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242215318616365131337/50000000000000000000)
  centralHi := (19377225489309210507/4000000000000000000)
  directionLo := (487000579071724898243/100000000000000000000)
  directionHi := (121750144767931224561/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree096.table
  base := (33581548762871705178578031831538114866201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-19183128036268737482964814399663185000000000000)
      constant := (486243307300915985970285585254989957021459706803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree096.table
  base := (6716309735878500332132012542369090968443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-6401539611762135393309271983551395000000000000)
      constant := (162437733296405518612551949619870425508348863215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487000579071724898243/100000000000000000000)
  centralHi := (121750144767931224561/25000000000000000000)
  directionLo := (244778515061413040091/50000000000000000000)
  directionHi := (489557030122826080183/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree097.table
  base := (35076659979612589957614064822969171429849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-174445803937249079675896001833488337500000000000)
      constant := (4469708100138441023173454970907735147883748122123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree097.table
  base := (2192291244275671162949770394909401479273/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-87320617945408002194451648593906371875000000000)
      constant := (2239769369982723151751341985484867392361541612168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244778515061413040091/50000000000000000000)
  centralHi := (489557030122826080183/100000000000000000000)
  directionLo := (492100200639227446719/100000000000000000000)
  directionHi := (1537813126997585771/312500000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree098.table
  base := (36598664275457575005429974786327996331137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-176243455548079522005108674070008010000000000000)
      constant := (4564222658263923328356248317631676086524999431299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree098.table
  base := (18299332107366163762962215485319815262631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-88220451132027176579228125409868911250000000000)
      constant := (2287128496681300956027978542869034209575325798837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492100200639227446719/100000000000000000000)
  centralHi := (1537813126997585771/312500000000000000)
  directionLo := (494630295468902891447/100000000000000000000)
  directionHi := (61828786933612861431/12500000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree099.table
  base := (4768445204334104676163085727284094048119/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-3297057539979814154339284190861623750000000000)
      constant := (86291360000865038198537139462633268746108546876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree099.table
  base := (19073780791443406101627460530946109841641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-3300751271060975961629800082438201875000000000)
      constant := (86480991836242089320148925725627872638608797041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494630295468902891447/100000000000000000000)
  centralHi := (61828786933612861431/12500000000000000000)
  directionLo := (497147514247170347219/100000000000000000000)
  directionHi := (24857375712358517361/5000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree100.table
  base := (39723352044017640573158046734155145549173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-179838758769740406663534018543047355000000000000)
      constant := (4756240445454846378772220247865710387515523615071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree100.table
  base := (7944670399971683723236400089682243678421/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-180040235010531050697562158083587980000000000000)
      constant := (4766688437317441210436308669418610496682759635835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497147514247170347219/100000000000000000000)
  centralHi := (24857375712358517361/5000000000000000000)
  directionLo := (249826025790262047347/50000000000000000000)
  directionHi := (99930410316104818939/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree101.table
  base := (41326035492353564794718248383796723719171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-181636410380570848992746690779567027500000000000)
      constant := (4853743674461440058295216814016669909693625377417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree101.table
  base := (8265207090940173720544306663174789420747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-181839901383769399467115111715513058750000000000)
      constant := (4864401627817284651723849445841905471139004843845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249826025790262047347/50000000000000000000)
  centralHi := (99930410316104818939/20000000000000000000)
  directionLo := (12553602430555366723/2500000000000000000)
  directionHi := (502144097222214668921/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree102.table
  base := (42955611970314938326910860560992882237601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-6793854147829677456368865296892100000000000000)
      constant := (183416412112736518146435918473841586539923767001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree102.table
  base := (10738902984553146203580750349561246392163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96386233594244105879061956194635000000000000)
      linear := (-10202198208722652679814892519302118750000000000)
      constant := (275728507257466229516896925922180031416609586178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12553602430555366723/2500000000000000000)
  centralHi := (502144097222214668921/100000000000000000000)
  directionLo := (252311918120012339561/50000000000000000000)
  directionHi := (504623836240024679123/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree103.table
  base := (2788255091876929327352879486211183286879/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-92615856801115866825586017626303186250000000000)
      constant := (2525869401591592601144059324403085975592913207464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree103.table
  base := (44612081442662804209745453022947032510291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-185439234130246097006221018979363216250000000000)
      constant := (5062822945750102924617644809037653530354155693657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252311918120012339561/50000000000000000000)
  centralHi := (504623836240024679123/100000000000000000000)
  directionLo := (507091449176660354963/100000000000000000000)
  directionHi := (126772862294165088741/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree104.table
  base := (46295443984890788140726978929334190079031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10265989376901739087710740896470000000000000)
      linear := (-1106682634396817609351388801710805000000000000)
      constant := (30486572206292194819103478414270005236898799773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree104.table
  base := (11573860990390152562773496481692757203823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5132994688450869543855370448235000000000000)
      linear := (-553961244093149247857319445595527500000000000)
      constant := (15276719151327660006125540339975885302284407818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507091449176660354963/100000000000000000000)
  centralHi := (126772862294165088741/25000000000000000000)
  directionLo := (995209203521781643/195312500000000000)
  directionHi := (509547112203152201217/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree105.table
  base := (24002849754673341662267383790307210993091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96386233594244105879061956194635000000000000)
      linear := (-10490389823549589906088743318091428750000000000)
      constant := (291873268115060067550503094468354805144354985473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree105.table
  base := (48005699489460150984377797930049122959239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-7001428402841584983160256527526421250000000000)
      constant := (195008796771006861451035644006255057774491425839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (995209203521781643/195312500000000000)
  centralHi := (509547112203152201217/100000000000000000000)
  directionLo := (51199099726563361321/10000000000000000000)
  directionHi := (511990997265633613211/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree106.table
  base := (1243571200968657018702164960933512816883/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-95312334217361530319405025981082695000000000000)
      constant := (2678101586397528146019149355016692387907264824820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree106.table
  base := (9948569604359273754840706128093736265511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-190838233249961143314879879875138452500000000000)
      constant := (5367942264744392196563365424700724686111598102985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51199099726563361321/10000000000000000000)
  centralHi := (511990997265633613211/100000000000000000000)
  directionLo := (514423272225843523903/100000000000000000000)
  directionHi := (8037863628528805061/1562500000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree107.table
  base := (51506889569192323569144975177207539535493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-192422320045553502968022724198685062500000000000)
      constant := (5459683743025898849024489271785445410253090461711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree107.table
  base := (25753444777373229539899145046266756488789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-96318949811599746042216416753531765625000000000)
      constant := (2735822664460571152705200766092655918339282835503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514423272225843523903/100000000000000000000)
  centralHi := (8037863628528805061/1562500000000000000)
  directionLo := (516844100995677980281/100000000000000000000)
  directionHi := (258422050497838990141/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree108.table
  base := (5329782409742386601863348946291268454419/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-3596666141784887875874729563614902500000000000)
      constant := (103040009939921065331938796040351143455467565095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree108.table
  base := (10659564817022605350859291018034254020883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-7201391333201401513110584708851430000000000000)
      constant := (206531359457026578777181389215103566093604805415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516844100995677980281/100000000000000000000)
  centralHi := (258422050497838990141/50000000000000000000)
  directionLo := (16226676364565495447/3125000000000000000)
  directionHi := (103850728733219170861/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree109.table
  base := (11023130324143227398702794155376193688363/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-196017623267214387626448068671724407500000000000)
      constant := (5669633553977995202681582535188007325379750976005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree109.table
  base := (27557825805112770578069990683911202839239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-98118616184838094811769370385456844375000000000)
      constant := (2841023196996835981158466612626387612465050507653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16226676364565495447/3125000000000000000)
  centralHi := (103850728733219170861/20000000000000000000)
  directionLo := (521652056630665565727/100000000000000000000)
  directionHi := (16301626769708298929/3125000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree110.table
  base := (890005814637438571757981657724636878133/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-98907637439022414977830370454122040000000000000)
      constant := (2888051397343592540311109778964231806284760639712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree110.table
  base := (28480186063928612289575512932428723576559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-99018449371457269196545847201419383750000000000)
      constant := (2894372197438815127629669268569369300029009681293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521652056630665565727/100000000000000000000)
  centralHi := (16301626769708298929/3125000000000000000)
  directionLo := (524039492704022624527/100000000000000000000)
  directionHi := (32752468294001414033/6250000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree111.table
  base := (29415992821885519927244651272625719740491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-3696535675719912449719878021199328750000000000)
      constant := (108954967757013679669812093283037747673644635891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree111.table
  base := (14707996409038739466179099632211738261089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96386233594244105879061956194635000000000000)
      linear := (-11102031395341827064591369335264658125000000000)
      constant := (327580039332617744263990869097833378247896456134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524039492704022624527/100000000000000000000)
  centralHi := (32752468294001414033/6250000000000000000)
  directionLo := (263208050617745946173/50000000000000000000)
  directionHi := (526416101235491892347/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree112.table
  base := (30365246070034384774125528374441426655661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-100705289049852857307043042690641712500000000000)
      constant := (2996014973274430426218511584823657290579954224647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree112.table
  base := (30365246066790082894240470231763031924549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-100818115744695617966098800833344462500000000000)
      constant := (3002567666659212766188172502493233766561338339023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263208050617745946173/50000000000000000000)
  centralHi := (526416101235491892347/100000000000000000000)
  directionLo := (105756405643622725333/20000000000000000000)
  directionHi := (264391014109056813333/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree113.table
  base := (3915993226524163453651442488251067051839/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-101604114855268078471649378808901548750000000000)
      constant := (3050743928847203588995078685540257890787690022824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree113.table
  base := (62655891618858964050693819649529497682183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-203435897862629584701750555298614003750000000000)
      constant := (6114828270868473725815251969214330333762628244341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105756405643622725333/20000000000000000000)
  centralHi := (264391014109056813333/50000000000000000000)
  directionLo := (132784354098324631747/25000000000000000000)
  directionHi := (531137416393298526989/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree114.table
  base := (64608184095648808688548556356115978743773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-22778431257929622141390158872702530000000000000)
      constant := (690215776923642328918836019587656826972016149919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree114.table
  base := (8076023011367514852080416462027278976059/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-3800658596960517286505620535750723750000000000)
      constant := (115287398530272712601018812725378633149079602636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132784354098324631747/25000000000000000000)
  centralHi := (531137416393298526989/100000000000000000000)
  directionLo := (266741202675662037447/50000000000000000000)
  directionHi := (106696481070264814979/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree115.table
  base := (66587369552970387036160555538742326134033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45630000000000000000000000000000000000000000
      center := (675324)
      previous := (337662)
      next := (337662)
      square := (3279682806609440275658062781670000000000000)
      linear := (-390932954503208018150707187317282500000000000)
      constant := (11953482703973243954949968319466717952899592579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree115.table
  base := (66587369548959596641837688877275821740353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45630000000000000000000000000000000000000000
      center := (675324)
      previous := (337662)
      next := (337662)
      square := (3279682806609440275658062781670000000000000)
      linear := (-391370946331013766050768360231501250000000000)
      constant := (11979601290387709204231416787075167973038730739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266741202675662037447/50000000000000000000)
  centralHi := (106696481070264814979/20000000000000000000)
  directionLo := (33488570726742023813/6250000000000000000)
  directionHi := (535817131627872381009/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree116.table
  base := (68593447995626774203111352668023157753533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-208601184543027483930936774327362115000000000000)
      constant := (6435838931959853452337920937357653219810737300791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree116.table
  base := (13718689598442134783876852749959164784203/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-208834896982344631010409416194389240000000000000)
      constant := (6449896956807882883041607938568654804892791874405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33488570726742023813/6250000000000000000)
  centralHi := (535817131627872381009/100000000000000000000)
  directionLo := (107628345759359691861/20000000000000000000)
  directionHi := (269070864398399229653/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree117.table
  base := (35313209711514064572945972577246541561587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (190110914387069242365013720305000000000000)
      linear := (-23054880139585571582308727434131250000000000)
      constant := (717650858753602825612662399756154748611079523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree117.table
  base := (3531320971005936814960996173011167857891/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (190110914387069242365013720305000000000000)
      linear := (-23080710426866423381543104298303125000000000)
      constant := (719217964410661144294522399737192769374493390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107628345759359691861/20000000000000000000)
  centralHi := (269070864398399229653/50000000000000000000)
  directionLo := (33778520472456705319/6250000000000000000)
  directionHi := (108091265511861457021/20000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree118.table
  base := (18171570958674429152917239882741532443927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-106098243882344184294681059400200730000000000000)
      constant := (3331860382738636549176550293036380865381553957258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree118.table
  base := (72686283832220034562788875736613207076887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-212434229728821328549515323458239397500000000000)
      constant := (6678267641825410918024051052269250382017530916549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33778520472456705319/6250000000000000000)
  centralHi := (108091265511861457021/20000000000000000000)
  directionLo := (27138052791485405243/5000000000000000000)
  directionHi := (542761055829708104861/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree119.table
  base := (74773041230253671862356256497926796720313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-213994139375518810918574791036921132500000000000)
      constant := (6779156017434612832358611263685002101415752967851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree119.table
  base := (74773041228143778162086828715049060573957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-214233896102059677319068277090164476250000000000)
      constant := (6793950452648139804382209279554540788698990403439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27138052791485405243/5000000000000000000)
  centralHi := (542761055829708104861/100000000000000000000)
  directionLo := (545056038817905204819/100000000000000000000)
  directionHi := (27252801940895260241/5000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree120.table
  base := (19221672902348407286360429780405727153059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-3996144277524986171255323393952607500000000000)
      constant := (127696064682530902406303704209806317326421255318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree120.table
  base := (76886691607597044393148609339123991874797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-24003729163922002898735692302454395000000000000)
      constant := (767847952853241466352726884452696096992796179791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545056038817905204819/100000000000000000000)
  centralHi := (27252801940895260241/5000000000000000000)
  directionLo := (68417674888596958381/12500000000000000000)
  directionHi := (547341399108775667049/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree121.table
  base := (15805446994376353295731952634911617906201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-217589442597179695577000135509960477500000000000)
      constant := (7013015191742871557630480688627273938797107206135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree121.table
  base := (79027234970352062789162361476908510355491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-217833228848536374858174184354014633750000000000)
      constant := (7028311010917961297898456031577055668161801274057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68417674888596958381/12500000000000000000)
  centralHi := (547341399108775667049/100000000000000000000)
  directionLo := (137404314184644126041/25000000000000000000)
  directionHi := (109923451347715300833/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree122.table
  base := (40597335658768944589990261840387389885681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-109693547104005068953106403873240075000000000000)
      constant := (3565719557046393178320056572346439901228083711187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree122.table
  base := (40597335658117751581172204122302503974603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-109816447610887361813863568992969856250000000000)
      constant := (3573494379182042858733382092320763322745879035681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137404314184644126041/25000000000000000000)
  centralHi := (109923451347715300833/20000000000000000000)
  directionLo := (275941864634257965099/50000000000000000000)
  directionHi := (551883729268515930199/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree123.table
  base := (41694500323114116760676899911201261694891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96386233594244105879061956194635000000000000)
      linear := (-12288041434380032235301415554611101250000000000)
      constant := (402825514439227235803939397968708940974729850873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree123.table
  base := (83389000645119453798128484264626604243271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-8201205985000484162862225615476473750000000000)
      constant := (269135734000638433301082595355929385116265170671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275941864634257965099/50000000000000000000)
  centralHi := (551883729268515930199/100000000000000000000)
  directionLo := (554140931855616359579/100000000000000000000)
  directionHi := (27707046592780817979/5000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree124.table
  base := (42805111478928860811383054028762698263739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-111491198714835511282319076109759747500000000000)
      constant := (3685637814591276859784494718960692527661866319153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree124.table
  base := (85610222956913825297316649254407107350673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-223232227968251421166833045249789870000000000000)
      constant := (7387339189877199782661655934884310022839952955571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554140931855616359579/100000000000000000000)
  centralHi := (27707046592780817979/5000000000000000000)
  directionLo := (556388977320989996793/100000000000000000000)
  directionHi := (278194488660494998397/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree125.table
  base := (21964584563090860168262955196935103155741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-112390024520250732446925412228019583750000000000)
      constant := (3746344110961012460646058237388890934974600661614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree125.table
  base := (10982292281444994611741358052992606415131/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-112515947170744884968192999440857474375000000000)
      constant := (3754505936971915185561641647012906756485084415348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556388977320989996793/100000000000000000000)
  centralHi := (278194488660494998397/50000000000000000000)
  directionLo := (4364281064184699657/781250000000000000)
  directionHi := (558627976215641556097/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree126.table
  base := (90133346529709154980339858690849643079109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-8391766690790070637891240618242920000000000000)
      constant := (282040631041645051220329191934032900815915423709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree126.table
  base := (45066673264512618473869270921220827200827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-4200584457680150346406276898400741250000000000)
      constant := (141327460559575013808451934166803667625706134627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4364281064184699657/781250000000000000)
  centralHi := (558627976215641556097/100000000000000000000)
  directionLo := (140214509220976676533/25000000000000000000)
  directionHi := (560858036883906706133/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree127.table
  base := (9243524778988068924248830980830186396959/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-114187676131081174776138084464539256250000000000)
      constant := (3869251038894846943906130627663765293184436760465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree127.table
  base := (231088119473246446829699540150132546861/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-114315613543983233737745953072782553125000000000)
      constant := (3877676089348417072410191709694916439331338159400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140214509220976676533/25000000000000000000)
  centralHi := (560858036883906706133/100000000000000000000)
  directionLo := (563079265524629242943/100000000000000000000)
  directionHi := (8798113523822331921/1562500000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree128.table
  base := (18952808406576409330080655933213152213347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-230173003872992791881488841165598185000000000000)
      constant := (7862903340917867098892531006087141077838433744845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree128.table
  base := (47382021016193308730138990941143540243803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-115215446730602408122522429888745092500000000000)
      constant := (3940009899691598292436869521051811468316078264081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563079265524629242943/100000000000000000000)
  centralHi := (8798113523822331921/1562500000000000000)
  directionLo := (282645883125087366541/50000000000000000000)
  directionHi := (565291766250174733083/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree129.table
  base := (242799323146830366808875731547073378939/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-4295752879330059892790768766705886250000000000)
      constant := (147931496805721883048826117458411542758230107800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree129.table
  base := (97119729258310515445553013979329960731179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-25803395537160351668288645934379473750000000000)
      constant := (889520636919576571997561760971886619981421901337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell101.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282645883125087366541/50000000000000000000)
  centralHi := (565291766250174733083/100000000000000000000)
  directionLo := (141873910285843353617/25000000000000000000)
  directionHi := (567495641143373414469/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree130.table
  base := (49751154733731042871005670197274617266863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5132994688450869543855370448235000000000000)
      linear := (-691622210339212060768976880587685000000000000)
      constant := (24007972004624593804985090944306199920922604229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree130.table
  base := (99502309467103279952352521967365712348881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10265989376901739087710740896470000000000000)
      linear := (-1384794237915275229492016373025682500000000000)
      constant := (48120414067312967502721517070395902438229067323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141873910285843353617/25000000000000000000)
  centralHi := (567495641143373414469/100000000000000000000)
  directionLo := (71211373789060059507/12500000000000000000)
  directionHi := (569690990312480476057/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree131.table
  base := (101911782659112837801731388201015938045021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-235565958705484118869126857875157202500000000000)
      constant := (8242084471080359067616674742883583257902148905367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree131.table
  base := (20382356531761502644959376770632427905353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-235829892580919862553703720673265421250000000000)
      constant := (8260012534682406499266499010236349041790910079655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71211373789060059507/12500000000000000000)
  centralHi := (569690990312480476057/100000000000000000000)
  directionLo := (285938955972118719773/50000000000000000000)
  directionHi := (571877911944237439547/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree132.table
  base := (52174074416866663658332194798058117816569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96386233594244105879061956194635000000000000)
      linear := (-13186867239795253399907751672870937500000000000)
      constant := (465026146003379936905728532429625528872757255507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree132.table
  base := (104348148833473526751491806309453042039119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-8801094776079933752713210159451500000000000000)
      constant := (310691607562809465375087050810593673286339277719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285938955972118719773/50000000000000000000)
  centralHi := (571877911944237439547/100000000000000000000)
  directionLo := (287028251177557109919/50000000000000000000)
  directionHi := (574056502355114219839/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree133.table
  base := (106811407991378814592517024744742596933147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-239161261927145003527552202348196547500000000000)
      constant := (8499853008504685484962220300386906253996097423569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree133.table
  base := (26702851997789440612795863642094215019683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-119714612663698280046404813968557789375000000000)
      constant := (4259166292958187473284945884814872478778351463682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287028251177557109919/50000000000000000000)
  centralHi := (574056502355114219839/100000000000000000000)
  directionLo := (57622685604080752957/10000000000000000000)
  directionHi := (576226856040807529571/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree134.table
  base := (27325390033027386303291978346910844010999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-120479456768987722928382437292358110000000000000)
      constant := (4315115806206022176005495934948737419045575366346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree134.table
  base := (109301560131921472423593195158595642090597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-241228891700634908862362581569040657500000000000)
      constant := (8648990079844112495566237330471277104679369484719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57622685604080752957/10000000000000000000)
  centralHi := (576226856040807529571/100000000000000000000)
  directionLo := (289194532862033800947/50000000000000000000)
  directionHi := (115677813144813520379/20000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree135.table
  base := (27954651313997405418857402355706434445367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-4495491947200109040481065681874738750000000000)
      constant := (162251971107093892551611145348202411344825510334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree135.table
  base := (3494331414244675514757668244729757626279/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-4500528853219875141331769170388254375000000000)
      constant := (162604553444059722478593497027418164988657752064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289194532862033800947/50000000000000000000)
  centralHi := (115677813144813520379/20000000000000000000)
  directionLo := (23221728896036868827/4000000000000000000)
  directionHi := (145135805600230430169/25000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree136.table
  base := (446728685012054930478119775831142605827/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-122277108379818165257595109528877782500000000000)
      constant := (4446988745308962396343326356263398503737832950912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree136.table
  base := (22872508672589988597536710857192837515147/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-244828224447111606401468488832890815000000000000)
      constant := (8913300004321876034297626822976478887003373687845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23221728896036868827/4000000000000000000)
  centralHi := (145135805600230430169/25000000000000000000)
  directionLo := (582689415385359755589/100000000000000000000)
  directionHi := (58268941538535975559/10000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree137.table
  base := (116933374453468017147361145476965406906491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-246351868370466772844402891294275237500000000000)
      constant := (9027344764916775053699765921640558231475624451057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree137.table
  base := (2338667489067044483294052152612867210541/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-123313945410174977585510721232407946875000000000)
      constant := (4523476217436116987467308236358151407048432510175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582689415385359755589/100000000000000000000)
  centralHi := (58268941538535975559/10000000000000000000)
  directionLo := (116965546470508757821/20000000000000000000)
  directionHi := (292413866176271894553/50000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree138.table
  base := (23906219705441223605406490080490551610427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (121469733578127417616965288210000000000000)
      linear := (-17373767414499559978549013759770000000000000)
      constant := (641441452263515471055691384275268891110810815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree138.table
  base := (59765549263553810535824515513185371806527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2535000000000000000000000000000000000000000
      center := (37518)
      previous := (18759)
      next := (18759)
      square := (182204600367191126425447932315000000000000)
      linear := (-26089850576936389827827598833936250000000000)
      constant := (964251541444073787677288530221002092880909189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116965546470508757821/20000000000000000000)
  centralHi := (292413866176271894553/50000000000000000000)
  directionLo := (586958259380600981807/100000000000000000000)
  directionHi := (36684891211287561363/6250000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree139.table
  base := (15269464448046492266013756873477248450309/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-124973585796063828751414117883657291250000000000)
      constant := (4648533991953573408192292092337737433139631090172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree139.table
  base := (122155715584288157924702402808103890649877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-250227223566826652710127349728666051250000000000)
      constant := (9317252232596759782280869662154251817204158149279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586958259380600981807/100000000000000000000)
  centralHi := (36684891211287561363/6250000000000000000)
  directionLo := (589081080991056041537/100000000000000000000)
  directionHi := (294540540495528020769/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree140.table
  base := (7800451601564846682950602902200100499177/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-125872411601479049916020454001917127500000000000)
      constant := (4716711964299507523418364582624033670901015363032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree140.table
  base := (124807225624966288156096508736110277785079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-252026889940065001479680303360591130000000000000)
      constant := (9453899599771276393038769887266261641620123887333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589081080991056041537/100000000000000000000)
  centralHi := (294540540495528020769/50000000000000000000)
  directionLo := (591196280187957030641/100000000000000000000)
  directionHi := (295598140093978515321/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree141.table
  base := (25497125729855028669238729743562450448183/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-28171386090420949129028175582261547500000000000)
      constant := (1063419566306174493350204154732602363706520125745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree141.table
  base := (127485628649214537595921327248980623976291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-9400983567159383342564194703426526250000000000)
      constant := (355242417746451685309026320832774056334416891691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591196280187957030641/100000000000000000000)
  centralHi := (295598140093978515321/50000000000000000000)
  directionLo := (148325984623936438781/25000000000000000000)
  directionHi := (4746431507965966041/800000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree142.table
  base := (65095462328578377606416771301524276251623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-127670063212309492245233126238436800000000000000)
      constant := (4854562244188493429522667508408932099484126391221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree142.table
  base := (130190924657105212391331748341846103881073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-255626222686541699018786210624441287500000000000)
      constant := (9730189270745691647725960434462442953361688796371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148325984623936438781/25000000000000000000)
  centralHi := (4746431507965966041/800000000000000000)
  directionLo := (74425516999490202659/12500000000000000000)
  directionHi := (595404135995921621273/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree143.table
  base := (6646155682437699713916157702276444084891/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5132994688450869543855370448235000000000000)
      linear := (-760762656909613688815618120453826250000000000)
      constant := (29137482554625553733419440761076789118019981530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree143.table
  base := (132923113648710161231228590718695762003961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10265989376901739087710740896470000000000000)
      linear := (-1523230112779763596380705113942996250000000000)
      constant := (58401370263585433470359186980524767467140074963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74425516999490202659/12500000000000000000)
  centralHi := (595404135995921621273/100000000000000000000)
  directionLo := (597496951362545611423/100000000000000000000)
  directionHi := (18671779730079550357/3125000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree144.table
  base := (135682195624137857815482210279316025101431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-9590201098010365524033022109256035000000000000)
      constant := (369955923778336767549526070281552181960093032831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree144.table
  base := (135682195624100583084938402759326763001551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-9600946497519199872514522884751535000000000000)
      constant := (370758229279818784875276657500725496939101660951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597496951362545611423/100000000000000000000)
  centralHi := (18671779730079550357/3125000000000000000)
  directionLo := (599582461896628913633/100000000000000000000)
  directionHi := (299791230948314456817/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree145.table
  base := (17308521322922321154094934104120236638041/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-130366540628555155739052134593216308750000000000)
      constant := (5065073502016061526014489713292953322132545371628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree145.table
  base := (69234085291673436523750932548498156559053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-130512610903128372663722535760108261875000000000)
      constant := (5076055559386684187366169326953042220982937975831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599582461896628913633/100000000000000000000)
  centralHi := (299791230948314456817/50000000000000000000)
  directionLo := (601660743559448733117/100000000000000000000)
  directionHi := (300830371779724366559/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree146.table
  base := (141281038526545451330051282873934055246391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-262530732867940753807316941422952290000000000000)
      constant := (10272480289514695479717202949707192656898230248357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree146.table
  base := (7064051926325925002594562392581086642039/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-131412444089747547048499012576070801250000000000)
      constant := (5147374179600444745888189479867461720868305732530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601660743559448733117/100000000000000000000)
  centralHi := (300830371779724366559/50000000000000000000)
  directionLo := (75466483875603988767/12500000000000000000)
  directionHi := (603731871004831910137/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree147.table
  base := (1801509993171335335340522531481394589487/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-4894970082940207335861659512212443750000000000)
      constant := (192885366638203239372737857302859601385914091480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree147.table
  base := (36030199863420977798394666517708525241359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96386233594244105879061956194635000000000000)
      linear := (-14701364141818524603697276599114815625000000000)
      constant := (579910217324324209011761824391954644483585165754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75466483875603988767/12500000000000000000)
  centralHi := (603731871004831910137/100000000000000000000)
  directionLo := (121159183522089032671/20000000000000000000)
  directionHi := (151448979402611290839/25000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree148.table
  base := (29397490672985988328848107029611648072701/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-266126036089601638465742285895991635000000000000)
      constant := (10560135530877123711278020857346111363161918183635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree148.table
  base := (5879498134596418329754595994654706078017/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-266424220925971791636103932415991760000000000000)
      constant := (10583017776684369761562403940021632030829538526475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121159183522089032671/20000000000000000000)
  centralHi := (151448979402611290839/25000000000000000000)
  directionLo := (7598161943851613301/1250000000000000000)
  directionHi := (607852955508129064081/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree149.table
  base := (37470250065070226781654435816413690092401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-133961843850216040397477479066255653750000000000)
      constant := (5352728743378650708259338234354647531863715057254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree149.table
  base := (7494050013013217131465207441758169911977/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-134111943649605070202828443023958419375000000000)
      constant := (5364324976870325644309653653292377032677895809790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7598161943851613301/1250000000000000000)
  centralHi := (607852955508129064081/100000000000000000000)
  directionLo := (60990305561331121979/10000000000000000000)
  directionHi := (609903055613311219791/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree150.table
  base := (152801440139824658014382293613871794437437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-29969037701251391458240847818781220000000000000)
      constant := (1205752851789296087008720279025176522508503915711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree150.table
  base := (152801440139810575745722598456997858873691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-10000872358238832932415179247401552500000000000)
      constant := (402788164555808787764628736020838600737416849091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60990305561331121979/10000000000000000000)
  centralHi := (609903055613311219791/100000000000000000000)
  directionLo := (152986571913383150057/25000000000000000000)
  directionHi := (611946287653532600229/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree151.table
  base := (155748773003624923460452965461699825055241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-271518990922092965453380302605550652500000000000)
      constant := (10999090068916367642107441463104521769082367217307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree151.table
  base := (31149754600722590394772231840690294875991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-271823220045686837944762793311766996250000000000)
      constant := (11022909244483081693238090327656180094509081137785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152986571913383150057/25000000000000000000)
  centralHi := (611946287653532600229/100000000000000000000)
  directionLo := (153495680049029867807/25000000000000000000)
  directionHi := (613982720196119471229/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree152.table
  base := (79361499425872104417334718316015053679333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-136658321266461703891296487421035162500000000000)
      constant := (5573700347597780435377458662171645196477623337391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree152.table
  base := (79361499425867016092018023621114233988789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-136811443209462593357157873471846037500000000000)
      constant := (5585768179084767785258281726494404335586456585503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153495680049029867807/25000000000000000000)
  centralHi := (613982720196119471229/100000000000000000000)
  directionLo := (616012420675032006227/100000000000000000000)
  directionHi := (154003105168758001557/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree153.table
  base := (161724117684243786411204811170027262907693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-10189418301620512967103912854762592500000000000)
      constant := (418396575738570087766320760598552672487460661893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree153.table
  base := (20215514710529391983951297784936148655569/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-5100417644299324731182753714363280625000000000)
      constant := (209651144149376794743220909661323886445232346676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616012420675032006227/100000000000000000000)
  centralHi := (154003105168758001557/25000000000000000000)
  directionLo := (309017727708459659427/50000000000000000000)
  directionHi := (123607091083383863771/20000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree154.table
  base := (164752129501183693342472731480861947417137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-276911945754584292441018319315109670000000000000)
      constant := (11447010618154007058214170263763362930073065553299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree154.table
  base := (164752129501176340363807461702317051474411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-277222219165401884253421654207542232500000000000)
      constant := (11471785522173660746364726764086195079378073080897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309017727708459659427/50000000000000000000)
  centralHi := (123607091083383863771/20000000000000000000)
  directionLo := (62005188966640939843/10000000000000000000)
  directionHi := (620051889666409398431/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree155.table
  base := (20975879287827841947491097737652845106243/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-139354798682707367385115495775814671250000000000)
      constant := (5799154957416773441859415342961644372436443887844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree155.table
  base := (167807034302616485790166814193198133526063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-279021885538640233022974607839467311250000000000)
      constant := (11623407572491619091102322392013983629453253573101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62005188966640939843/10000000000000000000)
  centralHi := (620051889666409398431/100000000000000000000)
  directionLo := (311030893805330614957/50000000000000000000)
  directionHi := (124412357522132245983/20000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree156.table
  base := (170888832088618496619027677561497274580739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (380221828774138484730027440610000000000000)
      linear := (-61474303961482616063871063727405000000000000)
      constant := (2575192950905139347534675601862752058253210931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree156.table
  base := (42722208022153296180271595308966651963027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (570332743161207727095041160915000000000000)
      linear := (-92314777091347331292744103047795000000000000)
      constant := (3871146592708862924761565403482154215830647698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311030893805330614957/50000000000000000000)
  centralHi := (124412357522132245983/20000000000000000000)
  directionLo := (624065212403205237611/100000000000000000000)
  directionHi := (156016303100801309403/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree157.table
  base := (86998761429613675064164438846054643278857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-141152450293537809714328168012334343750000000000)
      constant := (5951948589296977505871555196844252902906248555739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree157.table
  base := (173997522859222835557602304318604087800883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-282621218285116930562080515103317468750000000000)
      constant := (11929646609760022660414983326522617906592579509241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624065212403205237611/100000000000000000000)
  centralHi := (156016303100801309403/25000000000000000000)
  directionLo := (313031113093548552237/50000000000000000000)
  directionHi := (25042489047483884179/4000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree158.table
  base := (7085324264580179027066968538340491071451/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-284102552197906061757869008261188360000000000000)
      constant := (12058185145675092584479106323886206314163183824425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree158.table
  base := (177133106614500638906059730216567469649927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-284420884658355279331633468735242547500000000000)
      constant := (12084263596710737265687238786008534621031424340629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313031113093548552237/50000000000000000000)
  centralHi := (25042489047483884179/4000000000000000000)
  directionLo := (157013222529352245823/25000000000000000000)
  directionHi := (628052890117408983293/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree159.table
  base := (180295583354503876901991650733432049633559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-31766689312081833787453520055300892500000000000)
      constant := (1357052148469299324049782367774611475226619424477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree159.table
  base := (180295583354500616298036082804349078079619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-10600761149318282522266163791376578750000000000)
      constant := (453328847995282786354553750895903660562208518219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157013222529352245823/25000000000000000000)
  centralHi := (628052890117408983293/100000000000000000000)
  directionLo := (315018632191540564777/50000000000000000000)
  directionHi := (126007452876616225911/20000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree160.table
  base := (183484953079278401574407997470372359011593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-287697855419566946416294352734227705000000000000)
      constant := (12369749750239886573024337234406378800235876496411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree160.table
  base := (183484953079275630722516336138203782496897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-288020217404831976870739375999092705000000000000)
      constant := (12396492507245844160182233424036498071693137394819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315018632191540564777/50000000000000000000)
  centralHi := (126007452876616225911/20000000000000000000)
  directionLo := (79001926028519505721/12500000000000000000)
  directionHi := (632015408228156045769/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree161.table
  base := (186701215788879763098186704643917172560171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45630000000000000000000000000000000000000000
      center := (675324)
      previous := (337662)
      next := (337662)
      square := (3279682806609440275658062781670000000000000)
      linear := (-547250485879768220690939555710297500000000000)
      constant := (23680579182842713386426213856836408277142060273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree161.table
  base := (186701215788877408527030786080309070263371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45630000000000000000000000000000000000000000
      center := (675324)
      previous := (337662)
      next := (337662)
      square := (3279682806609440275658062781670000000000000)
      linear := (-547863674438696267751025197790203750000000000)
      constant := (23731766409887502665348516535009347123549261873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79001926028519505721/12500000000000000000)
  centralHi := (632015408228156045769/100000000000000000000)
  directionLo := (158496844993104082739/25000000000000000000)
  directionHi := (633987379972416330957/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree162.table
  base := (11871523217709910192140723865830339883983/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-5394317752615330205087401800134575000000000000)
      constant := (234912949049547083058221928038985197915243713464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree162.table
  base := (23743046435419570289987754189430420043517/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32128744531414701959687318731545000000000000)
      linear := (-5400362039839049526108245986350793750000000000)
      constant := (235420641974568363907682523367882232257366853268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158496844993104082739/25000000000000000000)
  centralHi := (633987379972416330957/100000000000000000000)
  directionLo := (317976618515723287359/50000000000000000000)
  directionHi := (635953237031446574719/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree163.table
  base := (193214420162764314609997917190465466273153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-293090810252058273403932369443786722500000000000)
      constant := (12844568333095247400273372831991820794276476086531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree163.table
  base := (193214420162762614569147706456952777264487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-293419216524547023179398236894867941250000000000)
      constant := (12872323214634571921989114055548157048009442361749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317976618515723287359/50000000000000000000)
  centralHi := (635953237031446574719/100000000000000000000)
  directionLo := (318956517968069410197/50000000000000000000)
  directionHi := (127582607187227764079/20000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree164.table
  base := (196511361827145466117657570730242481039571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-294888461862888715733145041680306395000000000000)
      constant := (13004833640983027072893185678035058892280304548217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree164.table
  base := (98255680913572010823418886833670326695383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-147609441448892685974475595263396510000000000000)
      constant := (6516465037427123344095681582277790638988636260741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318956517968069410197/50000000000000000000)
  centralHi := (127582607187227764079/20000000000000000000)
  directionLo := (319933416175830172213/50000000000000000000)
  directionHi := (639866832351660344427/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree165.table
  base := (7993407859061977015532068046385650375499/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-10988374573100709557865100515438002500000000000)
      constant := (487633154531073923600352613851664442136749652475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree165.table
  base := (199835196476548198112404051625449425307853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-33002061030113746746500460462079788750000000000)
      constant := (1466059471920647822240594801351509781551779598159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319933416175830172213/50000000000000000000)
  centralHi := (639866832351660344427/100000000000000000000)
  directionLo := (128362936219180351419/20000000000000000000)
  directionHi := (80226835136987719637/12500000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree166.table
  base := (50796481027755645941751890533114689350009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-149241882542274800195785193076672870000000000000)
      constant := (6664176463581632986951845655913423837811828348886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree166.table
  base := (4063718482220430821317792639226488739509/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-149409107822131034744028548895321588750000000000)
      constant := (6678569365964717526241944957056127389224944773575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128362936219180351419/20000000000000000000)
  centralHi := (80226835136987719637/12500000000000000000)
  directionLo := (80469579519677840199/12500000000000000000)
  directionHi := (643756636157422721593/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree167.table
  base := (206563544730610340286943553954351194584863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1734952204696393905823115211503430000000000000)
      linear := (-300281416695380042720783058389865412500000000000)
      constant := (13491606905455946768387733671735383341439946100701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree167.table
  base := (103281772365304727216771125888038450763551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (867476102348196952911557605751715000000000000)
      linear := (-150308941008750209128805025711284128125000000000)
      constant := (6760370264392585121185028033452572743846698769677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80469579519677840199/12500000000000000000)
  centralHi := (643756636157422721593/100000000000000000000)
  directionLo := (645692750712911912039/100000000000000000000)
  directionHi := (16142318767822797801/2500000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree168.table
  base := (209968058335357125647117735893590146855393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192772467188488211758123912389270000000000000)
      linear := (-33564340922912276116666192291820565000000000000)
      constant := (1517317456357460618742504686711100123157056968779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree168.table
  base := (41993611667071274614891102642173476675729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64257489062829403919374637463090000000000000)
      linear := (-11200649940397732112117148335351605000000000000)
      constant := (506864468068634934366165666774735234941434241645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell101.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645692750712911912039/100000000000000000000)
  centralHi := (16142318767822797801/2500000000000000000)
  directionLo := (647623077144177185163/100000000000000000000)
  directionHi := (161905769286044296291/25000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree169.table
  base := (213399464925306425941114774692612780812791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10265989376901739087710740896470000000000000)
      linear := (-1798087100100833889817801200372217500000000000)
      constant := (81781677706786789010029207296978093817099093853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 22331
  qDenominator := 43056
  table := BinomialMassData.Q22331_43056.Degree169.table
  base := (213399464925305786618953011140863449905893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10265989376901739087710740896470000000000000)
      linear := (-1800101862508740330158082595777623750000000000)
      constant := (81958219284813366777970626237852742303443369719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22331_43056.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell101.Kernel169
