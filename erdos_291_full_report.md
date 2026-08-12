# Erdős 问题 #291 完整研究报告

**日期**：2026-08-13
**来源**：https://www.erdosproblems.com/291 （状态 OPEN，数论）
**方法**：三轮共 12 个（子）agent 的并行攻坚 + 主 agent 独立复核，本文整合全部结果与勘误。

---

## 0. 摘要（TL;DR）

设 $L_n=\operatorname{lcm}(1,\dots,n)$，$a_n=\sum_{k=1}^n L_n/k$（故调和数 $H_n=a_n/L_n$）。Erdős #291 问：**$\gcd(a_n,L_n)=1$ 与 $\gcd(a_n,L_n)>1$ 是否都对无穷多个 $n$ 成立？**

- **一个方向已完全解决**：$\gcd(a_n,L_n)>1$ 无限次（构造 $n=2\cdot3^e$）。
- **核心方向仍开放**：$\gcd(a_n,L_n)=1$ 无限次（Shiu 2016 猜想）。这是本次攻坚的主战场。

三轮工作得到了：

1. **完全刻画**（已知，Steinerberger；本文重新推导并大规模核验）：$p\mid\gcd(a_n,L_n)\iff p\mid\text{分子}(H_{r_p})$，$r_p$ 为 $n$ 的 $p$ 进制首位。
2. **新结构**（本文）：坏位集 $E_p$ 是 Bernoulli 多项式 $B_{p-1}(x)-B_{p-1}$ 模 $p$ 的根集，把问题接到 Kummer/不规则素数理论。
3. **精确 iff 与若干双向等价**：素数幂影子形式、Kronecker 形式、覆盖系统形式。
4. **一批被排除的伪抓手**：坏位有界、Eswarathasan–Levine 猜想、Schanuel、具名等价、自举变换、素数幂间隙法——全部不闭合。
5. **最小充分假设** $H_A$（对维数一致的 Kronecker 下界）被精确定位——**没有任何已知猜想提供它**。
6. **勘误**：修正了此前报告的三处数学错误（计数、$J_p$ 误用、对数密度），并发现 Shiu 的 $x/\ln x$ 阶可能需修正。

---

## 1. 问题陈述

设
- $L_n=\operatorname{lcm}(1,2,\dots,n)$；
- $a_n=\sum_{k=1}^n L_n/k$（整数），使 $H_n=\sum_{k=1}^n 1/k=a_n/L_n$。

则 $\gcd(a_n,L_n)=\dfrac{L_n}{\operatorname{denom}(H_n)}$（调和数最低项分母与 $\operatorname{lcm}$ 的比值）。

**问题**：$\gcd(a_n,L_n)=1$ 与 $\gcd(a_n,L_n)>1$ 是否都对无穷多个 $n$ 成立？

---

## 2. 基础刻画（完全刻画）

**引理（刻画，已知但重新证明并逐项核验）。** 对素数 $p\le n$，记 $e=\lfloor\log_p n\rfloor$，$r_p=\lfloor n/p^e\rfloor\in\{1,\dots,p-1\}$（$n$ 的 $p$ 进制**首位数字**）。则

$$p\mid\gcd(a_n,L_n)\iff \sum_{j=1}^{r_p}\frac1j\equiv 0\pmod p\iff p\mid\text{分子}(H_{r_p}).$$

**证明概要**：记 $L_n=p^eL_n'$（$p\nmid L_n'$）。模 $p$ 考察 $a_n=\sum_k L_n/k$：$v_p(k)<e$ 的项 $\equiv0$；$v_p(k)=e$ 的项 $k=p^e j$（$j\le r_p$，$p\nmid j$）给出 $L_n/k=L_n'/j\equiv L_n'\cdot j^{-1}$。故 $a_n\equiv L_n'\sum_{j\le r_p}j^{-1}\pmod p$，而 $p\nmid L_n'$。∎

**直接推论**：

$$\gcd(a_n,L_n)=1\iff \text{对所有素数 }p\le n,\quad r_p\notin E_p,$$

其中 $E_p=\{r\in[1,p-1]:p\mid\text{分子}(H_r)\}$ 为 $p$ 的**坏位集**。

（该刻画已对 $1\le n\le2000$ 逐项用直接 $\gcd$ 计算核验，零失配。）

---

## 3. 坏位结构 $E_p$

### 3.1 基本性质

- **Wolstenholme（1862）**：$p\ge3$ 时 $p\mid\text{分子}(H_{p-1})$，故 $p-1\in E_p$ 恒成立。
- **对称性**：$H_{p-1-r}\equiv H_r\pmod p$，故 $r\in E_p\iff p-1-r\in E_p$。**额外坏位成对出现 $\{r,p-1-r\}$**，$|E_p|$ 恒为奇数。
- **小位安全表**（因 $\text{分子}(H_1)=1,\text{分子}(H_2)=3,\text{分子}(H_3)=11,\text{分子}(H_4)=25,\text{分子}(H_5)=137$）：

| 位 $r$ | 仅对哪些素数坏 |
|---|---|
| 1 | 无（$\text{分子}(H_1)=1$） |
| 2 | 仅 $p=3$ |
| 3 | 仅 $p=11$ |
| 4 | 仅 $p=5$（$25=5^2$） |
| 5 | 仅 $p=137$ |

故 $S_5=\{3,5,11,137\}$。

**坏位表（小 $p$）**：$E_3=\{2\}$，$E_5=\{4\}$，$E_7=\{6\}$，$E_{11}=\{3,7,10\}$，$E_{13}=\{12\}$，$E_{29}=\{13,15,28\}$，$E_{109}=\{25,31,44,64,77,83,108\}$（$|E_{109}|=7$）。

### 3.2 Bernoulli 多项式刻画（本文新结果，已验证）

**定理。** 对素数 $p$ 与 $1\le r\le p-1$：

$$(p-1)\,H_r\equiv B_{p-1}(r+1)-B_{p-1}\pmod p,$$

其中 $B_k(x)$ 为 Bernoulli 多项式，$B_k=B_k(0)$ 为 Bernoulli 数。因此

$$p\mid\text{分子}(H_r)\iff B_{p-1}(r+1)\equiv B_{p-1}\pmod p,$$

即 **$E_p$ 是多项式 $P(x)=B_{p-1}(x)-B_{p-1}$ 模 $p$ 的根集**（$r\mapsto r+1$ 平移）。

**证明**：由 $B_k(x+1)-B_k(x)=kx^{k-1}$ 求和得 $B_{p-1}(r+1)-B_{p-1}=(p-1)\sum_{x=1}^r x^{p-2}$；再由 Fermat 小定理 $x^{p-2}\equiv x^{-1}\pmod p$ 得 $\sum_{x\le r}x^{p-2}\equiv H_r$。∎

**结构事实**：$P(x)$ 的次数为 $p-2$，其模 $p$ 系数恰为偶 Bernoulli 数 $B_2,B_4,\dots,B_{p-3}$（由 Lucas 定理 $C(p-1,k)\equiv(-1)^k$）。$x=0$（即 $r=p-1$）恒为根 = Wolstenholme；额外根 = 额外坏位。**Glaisher（1900）**：$H_{p-1}\equiv-\tfrac{p^2}{3}B_{p-3}\pmod{p^3}$，故 Wolstenholme 素数 $\iff p\mid B_{p-3}$（不规则对 $(p,p-3)$；首个 Wolstenholme 素数 $16843$ 与 Johnson 表吻合）。

这使 $|E_p|$ 成为「$F_p$ 上显式多项式的根个数」问题。已知文献（Carlitz/Brillhart/Dilcher）只约束根的**重数**，不约束**个数**——个数恰为 $|E_p|$，仍是开放目标。

### 3.3 $|E_p|$ 的分布与界

- **无条件亚线性界**（Wu–Chen II，对 $J_p$ 的一致计数）：$|E_p|\le 3(p-1)^{2/3+1/(25\log p)}=O(p^{2/3+o(1)})$。
- **经验分布**（本文，$p\le5000$）：$P(|E_p|=1)=60.5\%$（无额外坏位），额外坏位**成对**，配对个数 $\sim\text{Poisson}(\tfrac12)$（$P(\text{无额外})=e^{-1/2}\approx0.607$，吻合）；均值 $|E_p|-1\approx0.98$（**不衰减**）。
- **关键推论**：$\sum_{p\le x}\frac{|E_p|-1}{p-1}\sim\ln\ln x$ **发散**，额外坏位**不可忽略**（渐近地几乎加倍 Wolstenholme 的贡献）。
- 与 OEIS 一致：A092194（H-不规则素数，密度 $\approx0.4$）与实测 39.5% 额外坏位率吻合；A098464（$\gcd=1$ 的 $n$）、A358557（补集）、A110566（$\gcd$ 值）。

---

## 4. 一个方向：$\gcd(a_n,L_n)>1$ 无限次（已证）

**定理。** $\gcd(a_n,L_n)>1$ 对无穷多个 $n$ 成立。

**证明**：取 $n=2\cdot3^e$（$e\ge1$）。其 3 进制表示为 $2\underbrace{00\cdots0}_e$，首位 $r_3=2$；而 $\sum_{j=1}^2\frac1j=1+\frac12=\frac32$，分子 $3$，$3\mid\text{分子}(H_2)$。由刻画 $3\mid\gcd(a_n,L_n)$。∎

（例：$n=6,18,54,162,\dots$ 均有 $3\mid\gcd$；直接验证 $\gcd(a_6,L_6)=3$ 等一致。）

---

## 5. 开放方向：$\gcd(a_n,L_n)=1$ 无限次（Shiu 2016，开放）

等价于「对所有 $p\le n$，首位 $r_p$ 避开坏位集 $E_p$」。本节列全部等价形式与规约。

### 5.1 双向等价

- **(E1)** $\gcd(a_n,L_n)=1\iff \operatorname{denom}(H_n)=\operatorname{lcm}(1,\dots,n)\iff$ 所有 $r_p\notin E_p$。
- **(E2 · 素数幂影子)** $n$ Wolstenholme-坏 $\iff$ 存在奇素数幂 $p^m$（$m\ge2$）落在 $(n,\ n+p^{m-1}]$ $\iff n\in\bigcup_{p,m\ge2}[p^m-p^{m-1},p^m)$。影子半宽 $=p^{m-1}\approx n/p\in[\sqrt n,\,n/3]$（$p=3$ 时最大 $n/3$）。
- **(E3 · Kronecker)** 好 $\iff$ 对所有 $p\le n$，$\{\log n/\log p\}\notin B_p$（$B_p=\{\log_p r,\log_p(r+1)\}$ 的坏位区间）。
- **(R1 · 覆盖系统)** $\#291\iff$ 坏区间族 $F=\{[rp^e,(r+1)p^e):p\ \text{素数},r\in E_p,e\ge1\}$ **不**余有限覆盖 $[N,\infty)$。

### 5.2 归约

- **（Grinberg–Kulikov / MathOverflow 486161）** 素数 $p>2n/\log n$ 自动为好，故只需对 $p\le 2n/\log n$ 避开坏位。
- **（$S_B$ 归约，本文）** 因 $r_p\le n/p$，若坏素数 $p\ge n/B$ 则 $r_p\le B$，故 $p$ 必落在**有限集** $S_B=\{p:\exists r\le B,\ p\mid\text{分子}(H_r)\}$。即「所有 $p\ge n/B$ 的坏素数都限于有限集 $S_B$」。
- **（种子构造）** $n_p=p^2-p-1$ **避开所有平方影子**（已证，零例外）；其立方坏性 $\iff\exists$ 素数 $q$ 使 $q^3-q^2<p^2-p\le q^3$（「$p$ 靠近 $q^{3/2}$」的丢番图语句）。

### 5.3 被排除的伪抓手（否定性结果）

| 假设/路线 | 结论 |
|---|---|
| 「对所有素数 $p$ 首位 $\le B$」 | **对所有充分大 $n$ 失败**（存在 $p\in(\tfrac n{B+2},\tfrac n{B+1}]$ 迫首位 $=B+1$，Nagura 素数间隔）。任何证明必须利用 $E_p$ 的稀疏性，而非首位有界。 |
| $|E_p|\le C$ 有界 | **不足**。配对引理证明坏密度级数仍发散。 |
| Eswarathasan–Levine 猜想（$J_p$ 有限） | **无推论**。见 §9.1 澄清。 |
| Schanuel 猜想（单独） | **不足**。只给有限素数版，缺「对维数一致」。见 §8.3。 |
| 具名开放问题的等价 | **不存在**。自成一类。 |
| 保持好性的变换（自举） | **不存在**。$n\to n+1,2n,n^2,n+L_n$ 全部 good→bad。 |
| 素数幂 $\sqrt n$ 间隙法 | **伪**。影子半宽是 $n/p$ 不是 $\sqrt n$。 |
| 相邻完全幂间隙 $\to\infty$ | 这是 **Pillai 猜想**，非定理（Tijdeman/Catalan 只解决间隙 1）。 |

---

## 6. 第一轮：五个子问题（A–E）

1. **A · 有限归约引理**：对固定 $B$，只有有限多素数使某个 $r\le B$ 坏，最紧界 $M_B=\max_{r\le B}\text{分子}(H_r)$。得到 $S_5=\{3,5,11,137\}$（见 §3.1）。
2. **B · 障碍定理**：对任意固定 $B$，「所有素数首位 $\le B$」对所有大 $n$ 失败（见 §5.3 第一行）。
3. **C · 素数 $n$ 刻画**：素数 $q$ 好 $\iff$ 对所有 $p<q$ 首位非坏位（$q$ 自身无害，$r_q=1$）。单固定素数：无穷多好素数（Bertrand）；双固定素数：PNT+Weyl；$\ge3$ 个素数需 $\{1/\ln p_j\}$ 的 $\mathbb Q$-线性无关（Schanuel 域）。**并给出精确计数 $G(10^6)=138902,\ G(10^7)=615233$**（见 §11）。
4. **D · 计数下界**：未能证 $G(x)\to\infty$（即 Shiu 猜想本身）。四个攻击的失效点被精确判定：并集界空泛（坏密度发散）；LLL 失效（所有位事件同依赖 $\log n$，无局部依赖图）；有限到无限无法提升（维数 $\sim x/\ln x$ vs 目标测度 $\sim1/\ln x$）；素数幂间隙归约撞同一稀疏命中问题。
5. **E · 文献**：确认 $J_p$ 有限仅对 $p\le7$ 已证、计算至 $p\le16843$（除 1381）；最小开放子引理＝避开 Wolstenholme 位。

---

## 7. 第二轮：四个新视角（2A–2D）

1. **2A · 素数幂影子**：严格化 E2；证明平方影子避开者 $=\bigcup_{p<Q}[p^2,Q^2-Q)$（密度 1）；种子 $n_p=p^2-p-1$ 避开所有平方影子；立方坏性 ⟺ 上述丢番图语句。
2. **2B · 坏位界**：$|E_p|=O(p^{2/3+o(1)})$（Wu–Chen II）；配对引理证「$|E_p|\le C$」不足；$S_B$ 归约确认。
3. **2C · Schanuel**：精确条件定理（见 §8.3）；**纠正**「好集对数密度 $\approx0.22$」的错误。
4. **2D · 等价/自举**：澄清 $J_p\neq E_p$（见 §9.1）；给出 E1/E2/E3；否定具名等价与自举。

---

## 8. 第三轮：反向分析与数论抓手（3A–3C）

### 8.1 数论抓手（3A）

**最重要成果 = Bernoulli 多项式刻画 $E_p$（§3.2，已独立复核正确）。**

次优：**Balister–Bollobás–Morris–Sahasrabudhe–Tiba 覆盖定理**（Invent. Math. 228, 2022）：相异模 + 权重和 $C$ ⟹ 未覆盖集密度 $\ge e^{-4C}/2$。最强的「正密度补集」工具，但为余类设计，需适配 #291 的首数/尾数块。

确认的否定：无「对维数一致」的对数线性型下界（Matveev $2^{6n+20}$、Baker–Wüstholz、Yu 皆超多项式）。

### 8.2 反向真：最小充分假设（3B）

**$H_{\min}=H_A$（$H_B$ 部分为假，见 §9.2）**，其中

$$H_A:\quad G(x)\ge(1-\varepsilon(x))\,x\prod_{p\le x}\Big(1-\tfrac{|E_p|}{p-1}\Big),$$

即「对维数一致」的**一侧（下界 / Janson 方向）Kronecker 等分布**。

**证明 $H_A(+H_B')\Rightarrow\#291$（模块化、严格）**：每 decade 的坏分数恰为 $c_p=|E_p|/(p-1)$；Mertens 型给出 $\sum c_p\sim\ln\ln x,\ \sum c_p^2<\infty$；故 $\prod(1-c_p)\asymp1/\ln x$；$H_A$ 给出 $G(x)\gg x/\ln x\to\infty$。

**必要性**：无自然等价。$H_A$、$H_B$ 皆不被 #291 蕴含，$H_{\min}$ 充分不必要。

### 8.3 Schanuel 的精确作用与缺口

**可证（有限素数版）**：设 $P$ 有限素数集，假设 $\{1/\ln p:p\in P\}$ 在 $\mathbb Q$ 上线性无关（$|P|=2$ 由唯一分解无条件成立；$|P|\ge3$ 由 Schanuel 推出，否则开放）。则 $G_P$（对 $P$ 中所有素数避开坏位）对数密度 $\prod_{p\in P}(1-\delta_p)>0$，故无限。

**精确关系**：$\{1/\ln p_j\}$ 无关 $\iff$ 乘积 $\prod_{i\ne j}\ln p_i$ 无关；Schanuel 作用于 $\ln p_j$ 给出代数无关，覆盖该假设。Baker（一次线性型）不适用；四指数是更弱 $2\times2$。

**关键缺口**：有限素数版**不能**推出 $G$ 无限——对数密度**不可数可加**，有限交的对数密度 $\prod(1-\delta_p)\to e^{-1.5}\approx0.22$，但无限交 $G$ 的对数密度实为 **0**。**Schanuel 单独不足以推出 $G(x)\to\infty$**；缺的是一个「对维数一致」的定量 Kronecker 界。

---

## 9. 反向双路的相容性与本质连接

### 9.1 澄清：Eswarathasan–Levine 与 #291 无关

两个被混为一谈的条件（已实测区分：$5\mid c_4,c_{20}$ 但 $5\nmid c_{100}$，尽管 100 的 5 进制首位是 4）：

- **弱（Shiu/#291）**：$p\mid\gcd(a_n,L_n)\iff v_p(a_n)\ge1\iff r_p\in E_p$；
- **强（E–L $J_p$）**：$p\mid\text{分子}(H_n)\iff v_p(a_n)\ge e+1$。

正确关系 **$E_p=J_p\cap[1,p-1]$**。Shiu 只依赖 $E_p$（天生有限）；E–L 猜想（$J_p$ 对所有 $n$ 有限）是更强断言，**对 #291 无推论**。

### 9.2 相容性裁决

3B 与 3C **核心相容**（都落在单一对象 $F$ 上），但有一处真矛盾：

$$\#291\ \overset{\text{3C 定性}}{\iff}\ F\ \text{不余有限覆盖}\ \overset{\text{3B 定量}}{\iff}\ H_A\ \text{成立}.$$

**真矛盾（已用数据裁决）**：3B 的 $H_B$（$\sum_p(|E_p|-1)/(p-1)<\infty$，额外坏位收敛）与 3C 的「额外坏位翻倍密度」冲突。实测（$p\le5000$，排除 $E_2=\varnothing$）：

$$\sum_{p\le5000}\frac{|E_p|-1}{p-1}\approx0.97,\quad \text{mean}(|E_p|-1)\approx0.98\ \text{不衰减}\ \Longrightarrow\ \sum_p\frac{|E_p|-1}{p-1}\sim\ln\ln x\ \text{发散}.$$

**∴ $H_B$ 为假**；3C 正确。额外坏位**不稀疏**。

### 9.3 本质连接

**$H_A$ 就是 3C 的 R1（「$F$ 不覆盖」）的定量正版本。** 3C 证明「#291 假的世界自洽、无反证」（故 $H_A$ 是真正非空的新假设）；3B 证明「要证 #291 真，只需假设 $H_A$」。两路把 #291 完整钉成一条：**定性覆盖状态 = 定量一致下界**。

---

## 10. 勘误（对早期报告错误的修正）

1. **计数偏高**：报告的 $G(10^6)=181007$、$G(10^7)=979344$ 是错的；精确值为 $138902$、$615233$（主代理独立筛法与 3C 一致）。$10^5$ 以下报告正确。
2. **额外坏位不可忽略**：报告的「额外坏位稀疏、误差可忽略」是错的——39.5% 的素数有额外坏位，成对 $\{r,p-1-r\}$，总密度发散。
3. **启发式推导两处错**：报告称「$\sum_p1/(p\ln p)$ 发散」——错，该级数**收敛**（$\approx1.5$）；发散的应是 $\sum_p1/p\sim\ln\ln x$。且 Benford 的 $\log_p(1+\tfrac1r)$ 是**对数密度**，非自然密度。
4. **对数密度自相矛盾**：早先「好集对数密度 $\approx0.22$ 为正、自然密度 0」自相矛盾（正对数密度必蕴含正上自然密度）。$e^{-1.5}$ 只是**有限近似极限**，好集 $G$ 的对数密度是 0。
5. **$J_p$（E–L）≠ $E_p$（Shiu）**：$E_p=J_p\cap[1,p-1]$；E–L 猜想与 #291 无关（§9.1）。
6. **影子宽度**：早先「$\sqrt n$」错；正确为 $n/p\in[\sqrt n,n/3]$。

---

## 11. 关键数值

| $x$ | $G(x)=\#\{n\le x:\gcd=1\}$ | 密度 | $G(x)\ln x/x$ |
|---|---|---|---|
| $10^3$ | 145 | 0.145 | 1.00 |
| $10^4$ | 2641 | 0.264 | 2.43 |
| $10^5$ | 20128 | 0.201 | 2.32 |
| $10^6$ | **138902** | 0.139 | 1.92 |
| $10^7$ | **615233** | 0.062 | 0.99 |

（$10^6,10^7$ 为修正后的精确值。$G\cdot\ln x/x$ 缓慢下降，与「密度 $\to0$、$G(x)\to\infty$」一致，但常数仍在缓慢振荡，难以据数据区分 $x/\ln x$ 与 $x/(\ln x)^{1+\alpha}$。）

**好素数**（$n$ 为素数且好）：$10^6$ 处 $11178$，$10^7$ 处 $42892$，密度 $\sim x/\ln^2 x$（与好整数密度吻合，支持「素性与好性独立」启发式）。

---

## 12. 最终评估与遗留缺口

### 12.1 已证（严格）

- $\gcd>1$ 无限次（$n=2\cdot3^e$）。
- 完全刻画 + Bernoulli 多项式刻画 $E_p$。
- 有限归约、$S_B$ 归约、素数幂影子形式、Kronecker 形式、覆盖系统形式（R1）。
- $|E_p|=O(p^{2/3+o(1)})$ 无条件界。
- 单/双素数情形（Bertrand / PNT+Weyl）。
- 否定性障碍：无首位有界族、无自举、$|E_p|\le C$ 不足、E–L 无推论、无具名等价、素数幂 $\sqrt n$ 间隙法伪。

### 12.2 开放（= Shiu 2016 猜想）

- $\gcd(a_n,L_n)=1$ 无限次；$G(x)\to\infty$。

### 12.3 被钉死的最小缺口

**证明 #291 需要一个「对维数一致」的定量 Kronecker 下界 $H_A$**：

$$G(x)\ge(1-\varepsilon(x))\,x\prod_{p\le x}\Big(1-\tfrac{|E_p|}{p-1}\Big).$$

现有一切已知猜想（Schanuel、Baker、四指数、Eswarathasan–Levine、覆盖系统）都**不**提供它——这是 #291 真正的、自成一类的困难。

### 12.4 对 Shiu 猜想的警示

由于额外坏位发散（$\sum(|E_p|-1)/(p-1)\sim\ln\ln x$），独立乘积模型给出 $G(x)\sim c\,x/(\ln x)^2$ 而非 $x/\ln x$。故要么 **Shiu 的 $x/\ln x$ 应修正为 $x/(\ln x)^{1+\alpha}$（$\alpha\approx1$ 或更慢缓变因子）**，要么真实 $G(x)$ 中存在某种**负相关**压制额外坏位的贡献——后者本身就是一个深刻的等分布结构事实。此点需单独核实，但鉴于 $H_A$ 只给下界，本文不作断言。

---

## 13. 参考文献

- P. Shiu, *The denominators of harmonic numbers*, arXiv:1607.02863 (2016, rev. 2024).
- A. Eswarathasan & E. Levine, *p-Integral harmonic sums*, Discrete Math. 91 (1991) 249–257.
- D. Boyd, *A p-adic study of the partial sums of the harmonic series*, Experiment. Math. 3 (1994) 287–302.
- C. Sanna, J. Number Theory 166 (2016) 41–46.
- B.-L. Wu & Y.-G. Chen, *On the denominators of harmonic numbers* I/II, C. R. Math. 356 (2018); J. Number Theory 200 (2019).
- B.-L. Wu & L.-J. Yan (IV), C. R. Math. 360 (2022) — 在 Schanuel 下 $\{\gcd>1\}$ 上密度 1。
- Carofiglio–Cherubini–Gambini (2025), on Eswarathasan–Levine and Boyd's conjectures.
- Balister–Bollobás–Morris–Sahasrabudhe–Tiba, Invent. Math. 228 (2022).
- Glaisher, Quart. J. Math. 31 (1900) — $H_{p-1}\equiv-\tfrac{p^2}{3}B_{p-3}\pmod{p^3}$.
- MathOverflow 486161 (2025) — Grinberg–Kulikov 的 $p>2n/\log n$ 归约。
- OEIS：A098464（$\gcd=1$ 的 $n$）、A358557（补集）、A110566（$\gcd$ 值）、A001008/A002805（$H_n$ 分子/分母）、A003418（$\operatorname{lcm}(1..n)$）、A092194（H-不规则素数）、A092101（harmonic 素数）。

---

*（附注：工作目录 /mnt/Data/erdos 下遗留若干探索脚本 explore.py、fast_good.py、families.py、interval2.py、power.py、analyze.py、verify_count.py、verify_extra.py 等，以及各轮子报告 subproblem*.md、erdos_291_*.md，均为探索产物，可清理或归档。）*
