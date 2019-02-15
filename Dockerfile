# Dockerfile for binder
# Reference: https://mybinder.readthedocs.io/en/latest/dockerfile.html#preparing-your-dockerfile

FROM sagemath/sagemath:8.6

RUN sage -pip install jupyterlab

RUN apt-get -qq update \
     && apt-get -qq install -y --no-install-recommends make \
     && apt-get -qq clean

RUN sage -i database_cremona_ellcurve

# Copy the contents of the repo in ${HOME}
COPY --chown=sage:sage . ${HOME}
