# FGA: Faster Gröbner Attack

This repository contains the implementation of the "Faster Gröbner Attack" (FGA) method for algebraic cryptanalysis of lightweight block ciphers, as described in the paper "Toward A More Efficient Gröbner-based Algebraic Cryptanalysis" by Hossein Arabnezhad-Khanoki and Babak Sadeghiyan.

**Paper Link:** [https://jcomsec.ui.ac.ir/article_24884_9daf850f015f16c38c431d919b691b3f.pdf](https://jcomsec.ui.ac.ir/article_24884_9daf850f015f16c38c431d919b691b3f.pdf)

## Overview

FGA is a novel algebraic attack method that combines the Forward-Backward (FWBW) representation of S-boxes with Universal Proning to efficiently solve the system of polynomial equations describing a cipher. This approach leads to improved performance in attacking lightweight block ciphers compared to previous methods.

This implementation focuses on the following ciphers:

*   **LBlock**
*   **MIBS**
*   **PRESENT**
*   **SKINNY**

## Key Features

*   **FWBW and MQ Representation:** Implements both Forward-Backward and Multivariate Quadratic representations of S-boxes, allowing for experimentation of the optimal representation for each cipher.
*   **Universal Proning:** Integrates the Universal Proning technique to recover linear relationships between intermediate state bits.
*   **PolyBoRi and M4RI Libraries:** Leverages the power of the PolyBoRi and M4RI libraries for Gröbner basis computation and efficient operations on Boolean matrices.
*   **Customizable Attack:** Provides options for configuring the attack parameters, such as the number of plaintexts and the type of S-box representation.
