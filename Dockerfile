ARG K_COMMIT
FROM runtimeverificationinc/kframework-k:ubuntu-bionic-${K_COMMIT}

RUN    apt-get update              \
    && apt-get upgrade --yes       \
    && apt-get install --yes       \
                       cmake       \
                       curl        \
                       pandoc      \
                       python3     \
                       python3-pip \
                       wget

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN groupadd -g $GROUP_ID user && useradd -m -u $USER_ID -s /bin/sh -g user user

USER user:user
WORKDIR /home/user

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain nightly --target wasm32-unknown-unknown
ENV PATH=/home/user/.cargo/bin:$PATH

RUN pip3 install --user     \
                 cytoolz    \
                 numpy      \
                 virtualenv

RUN    git clone 'https://github.com/WebAssembly/wabt' --branch 1.0.13 --recurse-submodules wabt \
    && cd wabt                                                                                   \
    && mkdir build                                                                               \
    && cd build                                                                                  \
    && cmake ..                                                                                  \
    && cmake --build .

ENV PATH=/home/user/wabt/build:$PATH

RUN wget -O erdpy-up.py https://raw.githubusercontent.com/ElrondNetwork/elrond-sdk/master/erdpy-up.py
RUN python3 erdpy-up.py
