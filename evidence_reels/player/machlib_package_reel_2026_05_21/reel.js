const REEL = {
  "cards": [
    {
      "id": "01-title",
      "title": "MachLib Evidence Tooling Update",
      "svg_path": "../../rendered/machlib_package_reel_2026_05_21/card_01_title.svg"
    },
    {
      "id": "02-published-packages",
      "title": "Published packages",
      "svg_path": "../../rendered/machlib_package_reel_2026_05_21/card_02_published_packages.svg"
    },
    {
      "id": "03-ready-pending",
      "title": "Ready / pending packages",
      "svg_path": "../../rendered/machlib_package_reel_2026_05_21/card_03_ready_pending.svg"
    },
    {
      "id": "04-passed-checks",
      "title": "Passed checks",
      "svg_path": "../../rendered/machlib_package_reel_2026_05_21/card_04_passed_checks.svg"
    },
    {
      "id": "05-pause-failure",
      "title": "Pause / failure",
      "svg_path": "../../rendered/machlib_package_reel_2026_05_21/card_05_pause_failure.svg"
    },
    {
      "id": "06-not-claimed",
      "title": "Not claimed",
      "svg_path": "../../rendered/machlib_package_reel_2026_05_21/card_06_not_claimed.svg"
    },
    {
      "id": "07-next-actions",
      "title": "Next actions",
      "svg_path": "../../rendered/machlib_package_reel_2026_05_21/card_07_next_actions.svg"
    }
  ],
  "narration": [
    {
      "title": "MachLib Evidence Tooling Update",
      "text": "This is a short evidence update for MachLib package tooling."
    },
    {
      "title": "Published packages",
      "text": "Four small pre-alpha packages are published and verified for early testing."
    },
    {
      "title": "Ready / pending packages",
      "text": "MachLib and adjacent tools remain in a careful readiness and retry path."
    },
    {
      "title": "What passed",
      "text": "The packet records tests, bounded validation, Twine checks, and repo artifact checks."
    },
    {
      "title": "What failed / paused",
      "text": "MachLib hit a PyPI rate limit, so the retry path pauses instead of forcing another upload."
    },
    {
      "title": "What is not claimed",
      "text": "This is evidence tooling, not a public proof claim or safety certification."
    },
    {
      "title": "Next actions",
      "text": "The next steps are cooldown, retry planning, and continued local AV product tooling."
    }
  ],
  "durationMs": 4000
};

let current = 0;
let playing = true;
let timer = null;

const cardImage = document.querySelector("[data-card-image]");
const cardTitle = document.querySelector("[data-card-title]");
const cardCounter = document.querySelector("[data-card-counter]");
const narrationTitle = document.querySelector("[data-narration-title]");
const narrationText = document.querySelector("[data-narration-text]");
const progress = document.querySelector("[data-progress]");
const playPause = document.querySelector("[data-play-pause]");

function sectionFor(index) {
  return REEL.narration[index] || { title: REEL.cards[index].title, text: "" };
}

function render() {
  const card = REEL.cards[current];
  const section = sectionFor(current);
  cardImage.src = card.svg_path;
  cardImage.alt = card.title;
  cardTitle.textContent = card.title;
  cardCounter.textContent = `${current + 1} / ${REEL.cards.length}`;
  narrationTitle.textContent = section.title;
  narrationText.textContent = section.text;
  progress.style.width = `${((current + 1) / REEL.cards.length) * 100}%`;
}

function next() {
  current = (current + 1) % REEL.cards.length;
  render();
}

function previous() {
  current = (current - 1 + REEL.cards.length) % REEL.cards.length;
  render();
}

function stopTimer() {
  if (timer) {
    window.clearInterval(timer);
    timer = null;
  }
}

function startTimer() {
  stopTimer();
  timer = window.setInterval(next, REEL.durationMs);
}

function setPlaying(value) {
  playing = value;
  playPause.textContent = playing ? "Pause" : "Play";
  if (playing) {
    startTimer();
  } else {
    stopTimer();
  }
}

document.querySelector("[data-next]").addEventListener("click", () => {
  next();
  if (playing) startTimer();
});

document.querySelector("[data-prev]").addEventListener("click", () => {
  previous();
  if (playing) startTimer();
});

playPause.addEventListener("click", () => setPlaying(!playing));

render();
setPlaying(true);
