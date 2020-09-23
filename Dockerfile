ARG K_COMMIT
FROM runtimeverificationinc/kframework-k:ubuntu-bionic-${K_COMMIT}

RUN    apt-get update         \
    && apt-get upgrade --yes  \
    && apt-get install --yes  \
                       cmake  \
                       pandoc \
                       python3

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN groupadd -g $GROUP_ID user && useradd -m -u $USER_ID -s /bin/sh -g user user

USER user:user
WORKDIR /home/user

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain nightly-2020-04-21 --target wasm32-unknown-unknown
ENV PATH=/home/user/.cargo/bin:$PATH

RUN    git clone 'https://github.com/WebAssembly/wabt' --branch 1.0.13 --recurse-submodules wabt \
    && cd wabt                                                                                   \
    && mkdir build                                                                               \
    && cd build                                                                                  \
    && cmake ..                                                                                  \
    && cmake --build .

ENV PATH=/home/user/wabt/build:$PATH
