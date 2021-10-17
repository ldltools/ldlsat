FROM debian:bullseye-slim as builder
MAINTAINER LDL Tools development team <ldltools@outlook.com>

ENV DEBIAN_FRONTEND noninteractive
ENV DEBIAN_PRIORITY critical
ENV DEBCONF_NOWARNINGS yes

ENV OCAML_VERSION "4.12.0"
ENV MONA_VERSION "1.4-18"

RUN echo "dash dash/sh boolean false" | debconf-set-selections;\
    dpkg-reconfigure -f noninteractive dash;\
    echo "/usr/local/lib" > /etc/ld.so.conf.d/usr-local-lib.conf;\
    apt-get update;\
    apt-get install -y build-essential flex bison gawk file rsync wget

# mona (http://www.brics.dk/mona)
RUN cd /root;\
    wget -q http://www.brics.dk/mona/download/mona-${MONA_VERSION}.tar.gz;\
    mkdir -p mona; cd mona;\
    tar --strip-components=1 -xzf ../mona-${MONA_VERSION}.tar.gz;\
    (./configure --prefix=/usr/local && make && make install-strip);\
    ldconfig

# opam2/ocaml
# note: opam2 activates sandboxing by default, which needs the "bubblewrap" package.
RUN cd /root;\
    apt-get install -y opam;\
    opam init -y --disable-sandboxing;\
    opam update;\
    opam switch create ${OCAML_VERSION};\
    touch /root/.bash_profile && cat /root/.opam/opam-init/init.sh >> /root/.bash_profile

# ldlsat
ADD . /root/ldlsat
RUN cd /root/ldlsat;\
    eval `opam config env`;\
    opam install -y ocamlfind ppx_deriving ppx_deriving_yojson;\
    make veryclean && make && PREFIX=/usr/local make install

WORKDIR /root
CMD ["/bin/bash"]

# ====================
# final image
# ====================
FROM debian:bullseye-slim

RUN echo "dash dash/sh boolean false" | debconf-set-selections;\
    dpkg-reconfigure -f noninteractive dash;\
    echo "/usr/local/lib" > /etc/ld.so.conf.d/usr-local-lib.conf;\
    apt-get update;\
    apt-get install -y gawk

COPY --from=builder /usr/local /usr/local

WORKDIR /root
CMD ["/bin/bash"]
